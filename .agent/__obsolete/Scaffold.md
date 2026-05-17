# Scaffold Steps

## File Structure Setup

- Create/revise the file structure for the Coq source as defined in [this](CodeStructure.md), including Lean
  directory/module, module aggregator, markdown reports.
- Do not delete existing file or directory.
- Do not remove any file contents.
- Doublecheck that:
    -[ ] Coq source file -> Lean module with aggregator.
    -[ ] Correct file structure in Lean module.

## Enforcing Code Discipline

- Delete all theorems in `Def.lean` and their entries in `Def.progress.md`.
- Delete all axioms in `Proof.lean`/`Auxiliary.lean` and their entries in `Proof.progress.md`.
- Delete all theorems with "True"/"False" type.
- Ensure that all lean code are consistent with [this](CodeStructure.md).

## Compile Progress Report

- Extract every definitions, axioms, types from the Coq source, ensure they are tracked in `Def.progress.md`.
- Extract every theorems, lemma and proofs from the Coq source, ensure they are tracked in `Proof.progress.md`.
- Double check to ensure that no Coq declaration is missed.

## Convert Theorems into Scaffolds

- Extract all theorems and lemmas from Coq source.
- Create (if not exists) theorem statements with `sorry` proof bodies in `Proof.lean` following conversion rules.
- DO NOT try to discharge the proofs.
- Revise `Proof.progress.md` to reflect your progress.
- Maintain original declaration order.
- Doublecheck that:
    -[ ] `Def.progress.md` ->`Def.lean`.
    -[ ] `Proof.progress.md` -> `Proof.lean`.
    -[ ] `Proof.lean` and `Auxiliary.lean` contains no axiom.
