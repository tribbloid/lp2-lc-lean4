### Code Structure

- All Lean production files and modules should be under [this](../Lp2lc/Active) module.
- All Lean test files and modules should be under [this](../Tests) module.
- A proof/module directory may contain these Lean files:
    1. `Def.lean`: definitions, types.
    2. `Proof.lean`: original theorems and proofs.
    3. `Auxiliary.lean`: auxiliary tactics and lemmas to support the original theorems.
- The above lean files in module aggregator (package.lean) to be compiled by `lake build`.
- `Glossary.md` may contain a list of lemmas and theorems, each annotated with a short explanation about its purpose.
- A `notes` subdirectory may contain memoranda that summarize requirements and specifications of the proof.
- Code shared between modules should be in `/Lp2lc/Active`.
