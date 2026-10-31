### Code & File Structure

- All Lean production files and modules should be under [this](../Lp2lc/Active) module.
- All Lean test files and modules should be under [this](../Tests) module.
- A Lean source directory may contain these files:
    - Lean source code:
        - `<module-name>Def.lean`: definitions, types, and supporting data structures.
        - `Hash.lean`: runtime JSON signatures, signature equality, and hashing for the module's syntax.
        - `Proof.lean`: theorems and proofs.
        - `mod.lean`: module aggregator; active imports compile modules, while import comments record
              disabled modules.
    - Markdown:
        - `TODO.md`: issues that can be fixed now or later.
        - `DEFECT.md`: defects of the current code that must be fixed immediately (otherwise will block or negatively
          affect the current task).

#### Issue Format

For all issues in markdown files:

- Each issue is a `- [ ]` or `- [x]` checkbox followed by a short name and indented fields:
    - **Summary:** Short description.
    - **Position:** Path to the problematic code and/or block comment that explains the issue, e.g.
      `src/path/to/file.lean (issue_summary)`.
      The block comment must be consistent with both code and documentation; every symbol should be annotated with a
      variable name in the code. The block comment should have the following sections:
        - always start with `TODO: issue_summary`.
        - detailed explanation.
        - recommended fix (if applicable).
    - **Refutation:** Path to the formal lean counterexample(s) & test case(s) that confirms & elaborates the issue.
- Delete the issue only when committing the fixed code.
