### File Structure
- All Coq sources should be [here](../Lp2lc_coq/Active)
- All converted Lean files and modules should be under [this](../Lp2lc/Active) module
- Each Coq file should be mapped to a Lean directory/module: `Lp2lc_coq/Active/<name>.v` → `Lp2lc/Active/<name>/`
- The directory always contains 4 files:
   1. `Def.lean`: definitions and axioms.
   2. `Proof.lean`: theorems and proofs.
   3. `Auxiliary.lean`: auxiliary tactics and lemmas to support the original proofs.
   4. `report.md`: progress report, always start with number of remaining "sorry".
  All these files should be imported into the Active module that can be compiled by `lake build`
- DO NOT write into any other files.
