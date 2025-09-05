# Task Definition

## Overview
You are an expert in programming language theory and Proof assistants (Coq and Lean 4). You are tasked with converting proofs from Coq to Lean 4 and verify it in a very safe, sandboxed environment.

## Workflow Steps
You should do the following tasks by the numbers. You should skip a task if it is already completed. If a task is partially completed, you should continue from where they left off:

### 1. Proof Implementation
- Discharge & implement proofs top-down approach.
- Replace `sorry` with complete proofs, use the original Coq proof as a reference.
- Add auxiliary tactics/lemmas to `Auxiliary.lean` as needed; do not add more theorem to `Proof.lean`.
- Do not delete or modify proofs that are already successfully verified.
- Build and verify after every iteration.
- After making progress by reducing the number of "sorry" in all files, update `report.md` to summarize your progress starting with number of remaining "sorry", then git commit into the current branch.

Repeat until all proofs are discharged and verified. Do not ask for permission.

## Conversion Rules
- Preserve original names (add `def_` prefix only if required by Lean syntax) and orders.
- Prefix each declaration with a comment indicating original Coq line number (strictly incremental).
- Use "sorry" with "TODO" comment for incomplete proofs.
- `Set`/`Prop` → Lean `Prop`.
- `Type` → Lean `Prop` (avoid `Type` unless necessary).
- `Var` from LibLN → Lean structure with `String` field.
- `Hint Constructors` → `@[aesop constructor]` attribute on type constructor.
- `Hint Resolve` → `@[aesop]` attribute on function (create wrapper functions if needed).
- `Lemma` → `Theorem`.
- `Tactic Notation` → Lean tactic macro with examples.
- `Ltac` → Lean elaborator with examples.
- `LibEnv` lemma reference `ok E` → a minimal abstract `ok : env → Prop` in `Aux.lean` to keep statements typechecking.

## Quality Checks
- [ ] All files compile without errors.
- [ ] No unused variable warnings.
- [ ] Line number references accurate.
- [ ] All theorems proven or marked with TODO.
- [ ] Aesop attributes properly applied.

## Success Criteria
- Complete 1:1 conversion of all declarations.
- Lean files build successfully with `lake build`.
- Proofs verified or explicitly marked as incomplete.
