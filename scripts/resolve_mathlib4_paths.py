#!/usr/bin/env python3
"""Resolve port-status mathlib4 paths to current mathlib4 HEAD paths.

Reads `port_status.yaml` (mathlib3 → mathlib4 paths at port time) and
walks mathlib4's git rename history forward to find each entry's
current path on master HEAD.

Output: `port_status_resolved.yaml` (sidecar). Schema per entry:

    algebra.group.basic:
      mathlib4_file: Mathlib/Algebra/Group/Basic.lean        # carried over
      current_mathlib4_file: Mathlib/Algebra/Group/Basic.lean
      resolution_status: verified
      rename_chain_length: 0
      resolved_at_commit: <mathlib4 master HEAD sha>

Statuses:
    verified           — port-time path still exists on master HEAD
    renamed            — followed rename chain to a live path
    deleted_to_parent  — file deleted; canonical falls back to the
                         closest parent directory that has a docs page
    deleted            — file deleted, no parent fallback (only when
                         --no-verify or --no-parent-fallback)
    unknown            — port-time path never appears in history
    unverified_404     — resolved path returned 404 from mathlib4_docs
"""
import argparse
import os
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
    p.add_argument("--port-status", default="port_status.yaml",
                   help="input wiki-mirrored YAML (default: port_status.yaml)")
    p.add_argument("--out", default="port_status_resolved.yaml",
                   help="output sidecar YAML (default: port_status_resolved.yaml)")
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


def parent_fallback(path: str, live: set, http_head):
    """For a deleted file, walk up directories looking for a live index page.

    Returns (current_path_to_index_html_source, hops) or (None, 0).
    """
    parts = path.split("/")
    if parts[-1].endswith(".lean"):
        parts = parts[:-1]
    while parts:
        # mathlib4_docs serves directory pages at <dir>/index.html, but the
        # corresponding source path doesn't exist as a .lean file. We probe
        # the URL directly in the verify pass; this just produces the
        # candidate index source path so verify_url can check it.
        candidate_url_path = "/".join(parts) + "/index.html"
        if http_head and http_head(candidate_url_path):
            # Reverse-engineer a "source path" representation. We use the
            # directory itself as the current_mathlib4_file (without the
            # trailing /index.html); the renderer will append .html.
            return ("/".join(parts), len(path.split("/")) - len(parts))
        parts = parts[:-1]
    return (None, 0)


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

    client = httpx.Client(http2=True, timeout=10.0,
                          limits=httpx.Limits(max_connections=concurrency))

    def check(path):
        try:
            r = client.head(MATHLIB4_DOCS + path, follow_redirects=True)
            return 200 <= r.status_code < 400
        except httpx.HTTPError:
            return False
    return check


def main():
    args = parse_args()
    here = Path.cwd()
    port_status_path = here / args.port_status

    print(f"[load] {port_status_path}", file=sys.stderr)
    text = port_status_path.read_text()
    if "```" in text:
        # wiki page wraps the YAML in a markdown fence
        parts = text.split("```")
        if len(parts) >= 3:
            text = parts[1]
    data = yaml.safe_load(text) or {}
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

    resolved = {}
    counts = {"verified": 0, "renamed": 0, "deleted_to_parent": 0,
              "deleted": 0, "unknown": 0, "unverified_404": 0,
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
        status, current, hops = resolve_path(port_path, renames, live, deletes)

        if status == "deleted" and not args.no_parent_fallback and http_head:
            parent, parent_hops = parent_fallback(port_path, live, http_head)
            if parent:
                status = "deleted_to_parent"
                current = parent  # directory path, no .lean suffix
                hops = parent_hops

        # Verification: HEAD probe for verified/renamed.
        if http_head and current and status in ("verified", "renamed"):
            url_path = current[:-5] + ".html"  # drop .lean
            if not http_head(url_path):
                status = "unverified_404"

        counts[status] = counts.get(status, 0) + 1
        resolved[module] = {
            "mathlib4_file": port_path,
            "current_mathlib4_file": current,
            "resolution_status": status,
            "rename_chain_length": hops,
            "resolved_at_commit": head_sha,
        }
    dt = time.time() - t0
    print(f"[resolve] {len(resolved)} entries in {dt:.1f}s", file=sys.stderr)
    for k, v in counts.items():
        print(f"  {k}: {v}", file=sys.stderr)

    out_path = here / args.out
    with out_path.open("w") as f:
        f.write("# Generated by scripts/resolve_mathlib4_paths.py.\n")
        f.write(f"# Source: port_status.yaml at mathlib4 {head_sha}.\n")
        f.write(f"# Rename threshold: -M{args.rename_threshold}%.\n")
        yaml.safe_dump(resolved, f, sort_keys=True, default_flow_style=False)
    print(f"[write] {out_path}", file=sys.stderr)


if __name__ == "__main__":
    main()
