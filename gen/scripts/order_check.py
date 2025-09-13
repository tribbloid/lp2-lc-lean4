#!/usr/bin/env python3
import re
from pathlib import Path
import argparse

MODULES = ["Dsubsup", "Ddia", "Dsub", "Fsub", "FsubL_alt"]

# Parse Coq index to ordered list of lemma/theorem names (dedup by first occurrence)
def coq_list(index_path: Path):
    idx = index_path.read_text(encoding="utf-8", errors="ignore").splitlines()
    items = []
    pat = re.compile(r"^(\d+):(Lemma|Theorem)\s+([A-Za-z0-9_]+)")
    for ln in idx:
        m = pat.match(ln)
        if m:
            items.append((int(m.group(1)), m.group(3)))
    items.sort(key=lambda x: x[0])
    seen, ordered = set(), []
    for _, name in items:
        if name in seen:
            continue
        seen.add(name)
        ordered.append(name)
    return ordered

# Extract Lean declaration names (theorem/lemma/axiom) in file order
def lean_list(proof_path: Path):
    text = proof_path.read_text(encoding="utf-8", errors="ignore")
    names = []
    pat = re.compile(r"\b(theorem|lemma|axiom)\s+([A-Za-z_][A-Za-z0-9_]*)\b")
    for m in pat.finditer(text):
        names.append(m.group(2))
    return names


def check_module(mod: str, base_idx: Path, base_src: Path):
    idx_path = base_idx / f"{mod}.coq.index"
    proof_path = base_src / mod / "Proof.lean"
    if not idx_path.exists():
        return mod, False, f"missing Coq index: {idx_path}"
    if not proof_path.exists():
        return mod, False, f"missing Lean file: {proof_path}"

    coq = coq_list(idx_path)
    lean = lean_list(proof_path)
    coq_set = set(coq)
    lean_filtered = [n for n in lean if n in coq_set]

    ok = (lean_filtered == coq)
    details = {
        "coq_count": len(coq),
        "lean_matching": len(lean_filtered),
        "order_ok": ok,
    }
    if not ok:
        # find first mismatch
        first_mismatch = None
        for i in range(min(len(coq), len(lean_filtered))):
            if coq[i] != lean_filtered[i]:
                first_mismatch = (i, coq[i], lean_filtered[i])
                break
        details["first_mismatch"] = first_mismatch
        if len(lean_filtered) != len(coq):
            details["lengths"] = (len(coq), len(lean_filtered))
    return mod, ok, details


def main():
    ap = argparse.ArgumentParser(description="Check that Lean Proof.lean declaration order matches Coq index order.")
    ap.add_argument("--modules", nargs="*", default=MODULES, help="Modules to check (default: %(default)s)")
    ap.add_argument("--base-idx", default="gen/plan/Define", help="Base directory for Coq index files")
    ap.add_argument("--base-src", default="Lp2lc/Active", help="Base directory for Lean modules")
    args = ap.parse_args()

    base_idx = Path(args.base_idx)
    base_src = Path(args.base_src)

    any_fail = False
    for mod in args.modules:
        mod_name, ok, info = check_module(mod, base_idx, base_src)
        if ok:
            print(f"=== {mod_name} === OK")
        else:
            any_fail = True
            print(f"=== {mod_name} === FAIL")
            print(info)
    exit(1 if any_fail else 0)

if __name__ == "__main__":
    main()
