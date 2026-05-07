#!/usr/bin/env python3
"""Audit canonical map by declaration-name overlap.

For each entry in mathlib4_canonical_map.yaml:
  - read the locally-rendered mathlib3 page (../html/<module-path>.html)
  - fetch the proposed mathlib4 page (cached under ~/.cache/doc-gen/m4_pages)
  - extract `id="..."` declaration anchors with at least one dot
  - compare lowercased sets

Reports each pair's recall (m3 ∩ m4 / m3) sorted ascending; the lowest
ones are the canonicals most likely to be wrong.
"""
import argparse
import re
import sys
import yaml
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from urllib.error import URLError, HTTPError
from urllib.request import urlopen

WT = Path(__file__).resolve().parent.parent
HTML_LOCAL = WT / "html"
M4_BASE = "https://leanprover-community.github.io/mathlib4_docs/"
M4_CACHE = Path.home() / ".cache" / "doc-gen" / "m4_pages"
ID_RE = re.compile(r'\bid="([^"]+)"')


def parse_args():
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--map", default=str(WT / "mathlib4_canonical_map.yaml"))
    p.add_argument("--top", type=int, default=50,
                   help="show this many lowest-overlap rows")
    p.add_argument("--min-decls", type=int, default=3,
                   help="skip mathlib3 pages with fewer decls (signal too weak)")
    p.add_argument("--concurrency", type=int, default=32)
    return p.parse_args()


_CAMEL_RE = re.compile(r"(?<!^)(?=[A-Z])")

def normalize_name(s):
    """Reduce snake_case / camelCase / PascalCase to a common minimal form.

    Applies the systematic mathlib3 → mathlib4 renames so equivalent
    declarations on either side compare equal:

      - camelCase / PascalCase → snake_case
      - drop instance / class / has prefixes
        (m3 `has_add` ↔ m4 `instAdd` → `add`)
      - drop the m4 big-operator `i` prefix
        (m3 `Union_decode₂` ↔ m4 `iUnion_decode₂` → `union_decode₂`,
         m3 `supr_decode₂`  ↔ m4 `iSup_decode₂`  → `sup_decode₂`)
      - reduce `cs` to `c` for conditionally-complete forms
        (m3 `cInf_empty` ↔ m4 `csInf_empty` → `c_inf_empty`)
    """
    s = _CAMEL_RE.sub("_", s).lower()
    for prefix in ("inst_", "has_", "is_"):
        if s.startswith(prefix):
            s = s[len(prefix):]
            break
    if s.startswith("i_") and len(s) > 2:
        s = s[2:]
    if s.startswith("cs_"):
        s = "c_" + s[3:]
    # mathlib3 named indexed sup/inf as `supr`/`infi`; mathlib4 uses `sup`/`inf`
    # (after dropping the `i_` prefix above the operator name remains).
    for old, new in (("supr_", "sup_"), ("infi_", "inf_")):
        if s.startswith(old):
            s = new + s[len(old):]
    return s

def extract_decls(html_text):
    """Normalized last-segment decl names from `id="..."` anchors.

    Comparing only the bare decl name (after the final `.`) is robust to
    mathlib4's `Foo` vs mathlib3's `foo` namespace casing. Normalizing
    camelCase to snake_case + stripping `inst_` is robust to mathlib4's
    style migration of definitions and instances.
    """
    out = set()
    for m in ID_RE.finditer(html_text):
        i = m.group(1)
        if "." not in i:
            continue
        last = i.rsplit(".", 1)[-1]
        # ignore short alphabetic-only ids and digit-only fragments
        if len(last) < 3 or last.isdigit():
            continue
        out.add(normalize_name(last))
    return out


def fetch_m4(rel_path):
    cache_path = M4_CACHE / rel_path
    if cache_path.exists():
        return cache_path.read_text(errors="replace")
    cache_path.parent.mkdir(parents=True, exist_ok=True)
    try:
        with urlopen(M4_BASE + rel_path, timeout=30) as r:
            text = r.read().decode(errors="replace")
            cache_path.write_text(text)
            return text
    except (URLError, HTTPError, TimeoutError):
        return None


def m3_html_path(module):
    return HTML_LOCAL / (module.replace(".", "/") + ".html")


def load_map(path):
    text = Path(path).read_text()
    return yaml.safe_load(text) or {}


def audit_one(module, m4_relpath, min_decls):
    m3p = m3_html_path(module)
    if not m3p.exists():
        return None
    m3_html = m3p.read_text(errors="replace")
    m3 = extract_decls(m3_html)
    if len(m3) < min_decls:
        return None
    m4_html = fetch_m4(m4_relpath + ".html")
    if m4_html is None:
        return None
    m4 = extract_decls(m4_html)
    inter = len(m3 & m4)
    return (inter / len(m3), len(m3), len(m4), inter, module, m4_relpath)


def main():
    args = parse_args()
    m = load_map(args.map)
    print(f"# {len(m)} entries in map", file=sys.stderr)

    rows = []
    with ThreadPoolExecutor(max_workers=args.concurrency) as ex:
        futures = {ex.submit(audit_one, mod, p4, args.min_decls): mod
                   for mod, p4 in m.items()}
        done = 0
        for f in as_completed(futures):
            r = f.result()
            done += 1
            if r is not None:
                rows.append(r)
            if done % 200 == 0:
                print(f"  {done}/{len(m)}", file=sys.stderr)

    rows.sort()
    print("recall\tm3\tm4\t∩\tmodule\tmathlib4_path")
    for r in rows[:args.top]:
        rec, n3, n4, inter, mod, p4 = r
        print(f"{rec:.3f}\t{n3}\t{n4}\t{inter}\t{mod}\t{p4}")

    if rows:
        n = len(rows)
        avg = sum(r[0] for r in rows) / n
        bad = sum(1 for r in rows if r[0] < 0.10)
        weak = sum(1 for r in rows if r[0] < 0.30)
        print(f"\n# audited: {n} pairs", file=sys.stderr)
        print(f"# avg recall: {avg:.3f}", file=sys.stderr)
        print(f"# recall <10%: {bad} ({100*bad/n:.1f}%)", file=sys.stderr)
        print(f"# recall <30%: {weak} ({100*weak/n:.1f}%)", file=sys.stderr)


if __name__ == "__main__":
    main()
