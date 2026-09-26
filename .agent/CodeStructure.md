### Code Structure

- All Lean production files and modules should be under [this](../Lp2lc/Active) module.
- All Lean test files and modules should be under [this](../Tests) module.
- A proof/module directory may contain these files:
    - Lean source code:
        - `<module-name>Def.lean`: definitions and types.
        - `Proof.lean`: original theorems and proofs.
        - `Auxiliary.lean`: auxiliary tactics and lemmas supporting the original theorems.
    - Issue lists in Markdown:
        - `TODO.md`: problems irrelevant to the current task that can be addressed later.
        - `DEFECT.md`: problems that may block or negatively affect the current task. Fix them systematically
          before the main task starts. Link to a self-contained counterexample or demo if possible, such as:
            - Inconsistent hypotheses that imply `False`.
            - Refutable or unprovable conjectures with counterexamples.
- List the above Lean files in the module aggregator (`package.lean`) so they are compiled by `lake build`.
- `Glossary.md` may contain a list of lemmas and theorems, each annotated with a short explanation about its purpose.
- A `notes` subdirectory may contain memoranda that summarize requirements and specifications of the proof.
- Code shared between modules should be in `/Lp2lc/Active`.
