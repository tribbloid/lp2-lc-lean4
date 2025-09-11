### File Structure

- All Coq sources should be [here](../Lp2lc_coq/Active)
- All converted Lean files and modules should be under [this](../Lp2lc/Active) module
- Each Coq file should be mapped to a Lean directory/module: `Lp2lc_coq/Active/<name>.v` → `Lp2lc/Active/<name>/`
    - These directories/modules are independent from each other, DO NOT import from lean file from a different module.
- The directory always contains 5 files:
    1. `Def.lean`: definitions, types and axioms.
    2. `Proof.lean`: theorems and proofs.
    3. `Auxiliary.lean`: auxiliary tactics and lemmas to support the original proofs.
    4. `Def.progress.md`: conversion progress of `Def.lean`, contains a table of 3 columns:
          - Coq name
          - Lean name
          - Category
    5. `Proof.progress.md`: conversion progress of `Proof.lean`, contains a table of 4 columns:
       - Coq theorem name
       - Lean theorem name
       - If the Lean theorem is discharged and proven (yes/no)
       - Category
    6. `specs.md`: clarify all ambiguity and choices in implementation. Read it first before asking questions.
- Each directory/module (including their parents `Lp2lc` and `Lp2lc/Active`) should be accompanied by a module aggregator lean file with imports
- Each `.md` file should be:
  - As detailed as possible. E.g. `Proof.progress.md` should list every lemma and theorems in Coq and Lean files.
  - Continuously revised and tracked by planning agent and be carried out by a sub-agent working on conversion.
- Code shared between modules are in `/Lp2lc/Active/Shared.lean`.
- DO NOT write into any other files.
