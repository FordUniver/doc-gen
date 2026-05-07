#!/usr/bin/env python3
"""Generate `mathlib4_canonical_map.yaml` for doc-gen's get_canonical_url.

Fetches the mathlib4-port-status YAML from the leanprover-community wiki,
walks each port-time mathlib4 path forward through mathlib4's git rename
history to its current master HEAD location (with an extra stem-match for
the X.lean → X/Basic.lean split pattern git misses), and writes a flat
`mathlib3_module: mathlib4/relative/path` map (no extension) for entries
that resolved to a live, web-reachable docs page.

Schema (flat, one entry per line):

    algebra.add_torsor: Mathlib/Algebra/AddTorsor/Basic
    algebra.algebra.basic: Mathlib/Algebra/Algebra/Basic
    ...

Modules with no live mathlib4 successor are omitted; the renderer falls
back to upstream's self-canonical for those.
"""
import argparse
import re
import subprocess
import sys
import time
from pathlib import Path

import yaml

MATHLIB4_REPO = "https://github.com/leanprover-community/mathlib4"
MATHLIB4_DOCS = "https://leanprover-community.github.io/mathlib4_docs/"
DEFAULT_CACHE = Path.home() / ".cache" / "doc-gen" / "mathlib4-history"


def parse_args():
    p = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    p.add_argument("--port-status", default=None,
                   help="local mathlib4-port-status YAML; default fetches from "
                        "the leanprover-community wiki")
    p.add_argument("--out", default="mathlib4_canonical_map.yaml",
                   help="output flat YAML (default: mathlib4_canonical_map.yaml)")
    p.add_argument("--cache", default=str(DEFAULT_CACHE),
                   help=f"mathlib4 clone cache (default: {DEFAULT_CACHE})")
    p.add_argument("--rename-threshold", default="75",
                   help="git -M<N>%% similarity threshold (default: 75)")
    p.add_argument("--no-fetch", action="store_true",
                   help="skip git fetch (use existing cache as-is)")
    p.add_argument("--no-verify", action="store_true",
                   help="skip HTTP HEAD verification of resolved URLs")
    p.add_argument("--no-parent-fallback", action="store_true",
                   help="for deletes, do not search for closest live parent")
    p.add_argument("--concurrency", type=int, default=50,
                   help="HTTP HEAD verification concurrency (default: 50)")
    return p.parse_args()


def ensure_clone(cache: Path, fetch: bool) -> Path:
    """Clone mathlib4 if missing; otherwise fetch latest master."""
    cache.parent.mkdir(parents=True, exist_ok=True)
    if not (cache / ".git").exists():
        print(f"[clone] {MATHLIB4_REPO} → {cache}", file=sys.stderr)
        subprocess.run(["git", "clone", MATHLIB4_REPO, str(cache)], check=True)
    elif fetch:
        print(f"[fetch] {cache}", file=sys.stderr)
        subprocess.run(["git", "-C", str(cache), "fetch", "origin", "master"], check=True)
    return cache


def head_commit(cache: Path) -> str:
    return subprocess.check_output(
        ["git", "-C", str(cache), "rev-parse", "origin/master"], text=True
    ).strip()


def live_paths_at_head(cache: Path) -> set:
    out = subprocess.check_output(
        ["git", "-C", str(cache), "ls-tree", "-r", "--name-only", "origin/master"],
        text=True,
    )
    return set(out.splitlines())


def parse_rename_log(cache: Path, threshold: str):
    """Return (renames, deletes).

    renames: dict[old_path, list[(commit_sha, new_path)]]
    deletes: dict[path, last_commit_sha]
    """
    cmd = [
        "git", "-C", str(cache), "log", "origin/master", "--reverse", "--no-merges",
        "--diff-filter=ACDMR", "--name-status", f"-M{threshold}%",
        "--pretty=format:COMMIT %H",
    ]
    print(f"[scan] {' '.join(cmd[3:])}", file=sys.stderr)
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, text=True, bufsize=1)
    renames: dict = {}
    deletes: dict = {}
    current_commit = None
    line_count = 0
    for line in proc.stdout:
        line = line.rstrip("\n")
        line_count += 1
        if not line:
            continue
        if line.startswith("COMMIT "):
            current_commit = line.split(" ", 1)[1]
            continue
        parts = line.split("\t")
        op = parts[0]
        if op.startswith("R") and len(parts) >= 3:
            old, new = parts[1], parts[2]
            renames.setdefault(old, []).append((current_commit, new))
            # A renamed path is no longer deleted; remove if previously marked.
            deletes.pop(old, None)
        elif op == "D" and len(parts) >= 2:
            deletes[parts[1]] = current_commit
        elif op == "A" and len(parts) >= 2:
            # Re-added at this path (after a delete); clear delete record.
            deletes.pop(parts[1], None)
    proc.wait()
    print(f"[scan] {line_count} log lines, {len(renames)} rename sources, "
          f"{len(deletes)} deletes", file=sys.stderr)
    return renames, deletes


def resolve_path(start: str, renames: dict, live: set, deletes: dict):
    """Walk renames forward from `start` to a HEAD-live path or a delete sink."""
    if start in live:
        return ("verified", start, 0)
    seen = {start}
    current = start
    hops = 0
    while current in renames:
        nxts = renames[current]
        # Take the latest rename event for this source.
        _, nxt = nxts[-1]
        if nxt in seen:
            break  # cycle
        seen.add(nxt)
        current = nxt
        hops += 1
        if current in live:
            return ("renamed", current, hops)
    if current in deletes:
        return ("deleted", None, hops)
    return ("unknown", None, hops)


def parent_fallback(path: str, live: set):
    """For a deleted file, find a successor by name-stem in the live tree.

    Handles only the unambiguous X.lean → X/Basic.lean (or X/Defs.lean)
    split pattern. Returning a successor in any other case risks pointing
    at an alphabetically-first but topically-wrong sibling (e.g. picking
    `Cat.lean` over `Pseudofunctor.lean`); when the heuristic can't
    decide, leave the entry unmapped so the renderer falls back to
    upstream's self-canonical.

    Returns (live_lean_path, 1) on a match, or (None, 0).
    """
    if not path.endswith(".lean"):
        return (None, 0)
    stem = path[:-5]
    for tail in ("Basic.lean", "Defs.lean"):
        candidate = f"{stem}/{tail}"
        if candidate in live:
            return (candidate, 1)
    return (None, 0)


# Basenames too generic to risk a same-basename rename match against
# (mathlib4 has 733 `Basic.lean`, 215 `Defs.lean` etc., so coincidental
# hits would dominate). The split fallback above handles these cases
# locally where it's safe.
_GENERIC_BASENAMES = frozenset({
    "Basic.lean", "Defs.lean", "Lemmas.lean", "Init.lean",
    "Util.lean", "Misc.lean", "Tactic.lean",
})


# Known directory-level renames in mathlib4 history that git's rename
# detection can't follow because the contained files were also rewritten.
# Each entry encodes the old → new directory segment; the fallback below
# tries `path.replace("/<old>/", "/<new>/")` for each. Verified empirically
# (old dir is empty in master HEAD, new dir is populated).
_DIRECTORY_ALIASES = {
    "GroupCat":            "Grp",            # Algebra/Category — 27 files in Grp
    "AlgebraCat":          "AlgCat",         # Algebra/Category — 4 files in AlgCat
    "SemiNormedGroupCat":  "SemiNormedGrp",  # Analysis/Normed/Group — 2 files
    "SlimCheck":           "Plausible",      # Testing — package renamed
}


def alias_fallback(path: str, live: set):
    """Try the deleted path with each known mathlib4 directory rename
    substituted in. Returns the first live match or (None, 0).
    """
    if not path.endswith(".lean"):
        return (None, 0)
    for old, new in _DIRECTORY_ALIASES.items():
        sep_old = f"/{old}/"
        sep_new = f"/{new}/"
        if sep_old in path:
            candidate = path.replace(sep_old, sep_new, 1)
            if candidate in live:
                return (candidate, 1)
    return (None, 0)


def basename_fallback(path: str, live: set):
    """For a deleted X.lean, find a live `*/X.lean` strictly *below* its
    original directory, with the same basename.

    Catches the case where mathlib4 pushed a file deeper into the same
    namespace (e.g. Mathlib/Algebra/GeomSum.lean →
    Mathlib/Algebra/Ring/GeomSum.lean) but git rename detection at -M75%
    missed it. Restricts to *subdirectory* matches (candidate's full
    directory chain must extend the deleted file's directory chain) so
    we don't conflate sibling renames like Group↔Ring or RBTree↔List
    that share the basename but have different content.

    Returns (live_lean_path, 1) on a unique match, or (None, 0).
    """
    if not path.endswith(".lean"):
        return (None, 0)
    parts = path.split("/")
    basename = parts[-1]
    if basename in _GENERIC_BASENAMES:
        return (None, 0)
    deleted_dir = parts[:-1]
    prefix = "/".join(deleted_dir) + "/"
    candidates = [p for p in live
                  if p.endswith("/" + basename)
                  and p != path
                  and p.startswith(prefix)]
    if len(candidates) == 1:
        return (candidates[0], 1)
    return (None, 0)


_SHIM_RE = re.compile(r"^\s*deprecated_module\b", re.MULTILINE)

def is_deprecated_shim(cache: Path, lean_path: str) -> bool:
    """Detect mathlib4 re-export shims that render as empty docs pages.

    These files exist in the source tree (so HEAD probes return 200) and
    git treats them as unrenamed, but their content is just
    `deprecated_module (since := ...)` and the rendered doc page has no
    declarations. Pointing canonical at them lands users on a dead page;
    treat them as deletions instead.
    """
    try:
        text = (cache / lean_path).read_text(errors="replace")
    except OSError:
        return False
    return bool(_SHIM_RE.search(text))


def make_url_checker(concurrency):
    """Return a callable url_path -> bool (200) using httpx if available."""
    try:
        import httpx
    except ImportError:
        print("[verify] httpx not installed; falling back to urllib (slow)",
              file=sys.stderr)
        from urllib.request import Request, urlopen
        from urllib.error import URLError, HTTPError

        def check(path):
            url = MATHLIB4_DOCS + path
            try:
                req = Request(url, method="HEAD")
                with urlopen(req, timeout=10) as r:
                    return 200 <= r.status < 400
            except (URLError, HTTPError):
                return False
        return check

    # GitHub Pages serves HTTP/2 if available; fall back to HTTP/1.1 if
    # the optional `h2` package isn't installed.
    try:
        client = httpx.Client(http2=True, timeout=10.0,
                              limits=httpx.Limits(max_connections=concurrency))
    except ImportError:
        client = httpx.Client(timeout=10.0,
                              limits=httpx.Limits(max_connections=concurrency))

    def check(path):
        try:
            r = client.head(MATHLIB4_DOCS + path, follow_redirects=True)
            return 200 <= r.status_code < 400
        except httpx.HTTPError:
            return False
    return check


PORT_STATUS_WIKI = ("https://raw.githubusercontent.com/wiki/leanprover-community/"
                    "mathlib/mathlib4-port-status-yaml.md")


def load_port_status(local_path):
    """Return the port-status YAML data, fetching from the wiki if needed."""
    if local_path is None:
        from urllib.request import urlopen
        print(f"[fetch] {PORT_STATUS_WIKI}", file=sys.stderr)
        text = urlopen(PORT_STATUS_WIKI, timeout=30).read().decode()
    else:
        text = Path(local_path).read_text()
    if "```" in text:
        # wiki page wraps the YAML payload in a markdown fence
        parts = text.split("```")
        if len(parts) >= 3:
            text = parts[1]
    return yaml.safe_load(text) or {}


def main():
    args = parse_args()
    data = load_port_status(args.port_status)
    print(f"[load] {len(data)} entries", file=sys.stderr)

    cache = ensure_clone(Path(args.cache).expanduser(), fetch=not args.no_fetch)
    head_sha = head_commit(cache)
    live = live_paths_at_head(cache)
    print(f"[head] origin/master = {head_sha[:12]} ({len(live)} live files)",
          file=sys.stderr)

    renames, deletes = parse_rename_log(cache, args.rename_threshold)

    http_head = None
    if not args.no_verify:
        http_head = make_url_checker(args.concurrency)

    resolved = {}            # module → mathlib4 docs path (no extension)
    counts = {"verified": 0, "renamed": 0, "split": 0, "aliased": 0, "moved": 0,
              "shim": 0, "deleted": 0, "unknown": 0, "unverified_404": 0,
              "not_ported": 0}

    t0 = time.time()
    for module, entry in data.items():
        if not isinstance(entry, dict):
            continue
        if not entry.get("ported"):
            counts["not_ported"] += 1
            continue
        port_path = entry.get("mathlib4_file")
        if not port_path or not port_path.endswith(".lean"):
            continue
        status, current, _ = resolve_path(port_path, renames, live, deletes)

        if status == "deleted" and not args.no_parent_fallback:
            parent, _ = parent_fallback(port_path, live)
            if parent:
                status = "split"
                current = parent
            else:
                aliased, _ = alias_fallback(port_path, live)
                if aliased:
                    status = "aliased"
                    current = aliased
                else:
                    moved, _ = basename_fallback(port_path, live)
                    if moved:
                        status = "moved"
                        current = moved

        # Drop entries whose mathlib4 target is a `deprecated_module`
        # re-export shim — the file exists (HEAD probes 200) but the
        # docs page renders empty.
        good_statuses = ("verified", "renamed", "split", "aliased", "moved")
        if current and status in good_statuses:
            if is_deprecated_shim(cache, current):
                status = "shim"
                current = None

        if http_head and current and status in good_statuses:
            if not http_head(current[:-5] + ".html"):
                status = "unverified_404"
                current = None

        counts[status] = counts.get(status, 0) + 1
        if current and current.endswith(".lean"):
            resolved[module] = current[:-5]  # drop .lean for the URL stub
    dt = time.time() - t0
    print(f"[resolve] {len(data)} input entries in {dt:.1f}s", file=sys.stderr)
    for k, v in counts.items():
        print(f"  {k}: {v}", file=sys.stderr)
    print(f"[resolve] mapped: {len(resolved)}", file=sys.stderr)

    out_path = Path(args.out)
    ported = sum(v for k, v in counts.items() if k != "not_ported")
    with out_path.open("w") as f:
        f.write("# Generated by scripts/resolve_mathlib4_paths.py — do not edit.\n")
        f.write(f"# Source: mathlib4-port-status wiki, mathlib4 master @ {head_sha}.\n")
        f.write(f"# Rename threshold: -M{args.rename_threshold}%. "
                f"Coverage: {len(resolved)}/{ported} = "
                f"{100*len(resolved)/ported:.1f}% of ported mathlib3 modules.\n")
        yaml.safe_dump(resolved, f, sort_keys=True, default_flow_style=False)
    print(f"[write] {out_path}", file=sys.stderr)


if __name__ == "__main__":
    main()
