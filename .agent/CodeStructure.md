### Code Structure

- All Lean production files and modules should be under [this](../Lp2lc/Active) module.
- All Lean test files and modules should be under [this](../Tests) module.
- A proof/module directory may contain these files:
    - Lean source code:
        - `<module-name>Def.lean`: definitions, types.
        - `Proof.lean`: original theorems and proofs.
        - `Auxiliary.lean`: auxiliary tactics and lemmas to support the original theorems.
    - List of issues in markdown:
        - `TODO.md`: problems in code irrelevant to current task, can be addressed later
        - `DEFECT.md`: problems in code that may block or negatively affect current task. The agent can still complete the task, but more fundamental & systematic fix are recommended
- List the above Lean files in the module aggregator (`package.lean`) so they are compiled by `lake build`.
- `Glossary.md` may contain a list of lemmas and theorems, each annotated with a short explanation about its purpose.
- A `notes` subdirectory may contain memoranda that summarize requirements and specifications of the proof.
- Code shared between modules should be in `/Lp2lc/Active`.
