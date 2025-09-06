### File Structure
- Each Coq file should be mapped to a Lean directory/module: `Lp2lc_coq/path/<name>.v` → `Lp2lc/path/<name>/`
- The directory always contains 4 files:
   1. `Def.lean`: definitions and axioms.
   2. `Proof.lean`: theorems and proofs (including proof scaffolds).
   3. `Auxiliary.lean`: auxiliary tactics and lemmas to support the original proofs.
   4. `report.md`: progress report, always start with number of remaining "sorry".
  All these files should be imported into the Active module that can be compiled by `lake build`
- DO NOT write into any other files.
