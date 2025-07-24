# Task Definition

## Overview
You are an expert in programming language theory and Proof assistants (Coq and Lean 4). You are tasked with converting proofs from Coq to Lean 4 and verify it in a very safe, sandboxed environment.

## Workflow Steps
Execute the following tasks sequentially. Do not create duplicated entries or files. If a task is half-done, continue
from where they left off.

### 1. File Structure Setup
- Create/revise the file structure for the Coq source as defined in [this](CodeStructure.md), including Lean
  directory/module, module aggregator, markdown reports.
- Do not delete existing file or directory.
- Do not remove any file contents.
- Doublecheck that:
  -[ ] Coq source file -> Lean module with aggregator.
  -[ ] Correct file structure in Lean module.

### 2. Enforcing Code Discipline
- Delete all theorems in `Def.lean` and their entries in `Def.progress.md`.
- Delete all axioms in `Proof.lean`/`Auxiliary.lean` and their entries in `Proof.progress.md`.
- Ensure that all lean code are consistent with [this](CodeStructure.md).

### 3. Compile Progress Report
- Extract every definitions, axioms, types from the Coq source, ensure they are tracked in `Def.progress.md`.
- Extract every theorems, lemma and proofs from the Coq source, ensure they are tracked in `Proof.progress.md`.
- Double check to ensure that no Coq declaration is missed.

### 4. Convert Theorems into Scaffolds
- Extract all theorems and lemmas from Coq source.
- Create (if not exists) theorem statements with `sorry` proof bodies in `Proof.lean` following conversion rules.
- DO NOT try to discharge the proofs.
- Revise `Proof.progress.md` to reflect your progress.
- Maintain original declaration order.
- Doublecheck that:
  -[ ] `Def.progress.md` ->`Def.lean`.
  -[ ] `Proof.progress.md` -> `Proof.lean`.
  -[ ] `Proof.lean` and `Auxiliary.lean` contains no axiom.

## Rules

see [this](ConversionRules.md)