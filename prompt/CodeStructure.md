### Code Structure

- All Coq sources should be [here](../Lp2lc_coq/Active)
- All converted Lean files and modules should be under [this](../Lp2lc/Active) module
- Each Coq file should be mapped to a Lean directory/module: `Lp2lc_coq/Active/<name>.v` → `Lp2lc/Active/<name>/`
    - These directories/modules are independent from each other, DO NOT import from lean file from a different module.
- The directory always contains 5 files:
    1. `Def.lean`: definitions, types and axioms.
    2. `Proof.lean`: original theorems and proofs, no axiom allowed.
    3. `Auxiliary.lean`: auxiliary tactics and lemmas to support the original theorems, no axiom allowed.
    4. `Def.progress.md`: conversion progress of `Def.lean`, contains a table of 3 columns:
        - Coq name
        - Lean name
        - Category
    5. `Proof.progress.md`: conversion progress of `Proof.lean`, contains a table of 4 columns:
        - Coq theorem name
        - Lean theorem name
        - If the Lean theorem is discharged and proven (yes/no)
        - Category
    6. `question.md`: questions and answers to clarify all ambiguity and choices in implementation.
- Each directory/module (including their parents `Lp2lc` and `Lp2lc/Active`) should be accompanied by a module
  aggregator lean file with imports
- In addition, types and axioms shared between modules should be in `Lp2lc/Active/Shared.lean`, these include:
    - `ok : env → Prop` axiom
- Each `.md` file should be:
    - As detailed as possible. E.g. `Proof.progress.md` should list every lemma and theorems in Coq and Lean files.
    - Continuously revised and tracked by planning agent and be carried out by a sub-agent working on conversion.
- Code shared between modules are in `/Lp2lc/Active/Shared.lean`.
- DO NOT write into any other files.
