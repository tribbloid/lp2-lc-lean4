### Code Structure

- All Lean production files and modules should be under [this](../Lp2lc/Active) module.
- All Lean test files and modules should be under [this](../Tests) module.
- A Lean source directory may contain these files:
    - Lean source code:
        - `<module-name>Def.lean`: definitions, types, and supporting data structures.
        - `Proof.lean`: theorems and proofs.
        - `package.lean`: module aggregator; active imports compile modules, while import comments record
              disabled modules.
    - Markdown documents:
        - `TODO.md`: problems irrelevant to the current task that can be addressed later.
        - `DEFECT.md`: problems that may block or negatively affect the current task. Fix them systematically
              before the main task starts. Link to a self-contained counterexample or demo if possible, such as:
            - Inconsistent hypotheses that imply `False`.
            - Refutable or unprovable conjectures with counterexamples.
        - `Glossary.md`: contains a list of major theorems with short explanations of their purpose.
- Code shared between modules should be in `/Lp2lc/Active`.
