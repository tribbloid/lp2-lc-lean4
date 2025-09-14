# Task Definition

## Overview

You are an expert in programming language theory and Proof assistants (Coq and Lean 4). You are tasked with converting
proofs from Coq to Lean 4 and verify it in a very safe, sandboxed environment.

## Workflow Steps

### 1. Source Scan
- Scan all Coq sources and rank them by size (in ascending order).
- Read the Lean build file [here](../lakefile.lean)

### 2. Locate File Structure

For each Coq source file:

- Find the corresponding file structure as defined in [this](CodeStructure.md).

### 3. Conversion

For each pair of Coq source file and Lean module, execute the following tasks sequentially.

Build the project to verify that your code is imported, compiled, and correct. Do this after every step and iteration.

If a task is half-done, continue from where they left off.

#### 1. Enforce Code Structure
- Delete all theorems in `Def.lean`, including their entries in `Def.progress.md`.
- Delete all axioms in `Proof.lean` and `Auxiliary.lean`, including their entries in `Proof.progress.md`.

#### 2. Convert Definitions
- Extract all definitions, axioms, types from Coq source.
- Convert to Lean 4 syntax following conversion rules.
- Write to `Def.lean` with original line number comments.
- Revise `Def.progress.md` to reflect your progress.

#### 3. Convert Theorems into Scaffolds
- Extract all theorems and lemmas from Coq source.
- Create theorem statements with `sorry` proof bodies in `Proof.lean` following conversion rules.
- Revise `Proof.progress.md` to reflect your progress.
- DO NOT try to discharge the proofs.
- Maintain original declaration order.

#### 4. Checklist
Check the following criteria, ensure that:

[ ] Each `Def.progress.md` entry is defined in `Def.lean` and the original Coq source.
[ ] Each `Proof.progress.md` entry is defined `Proof.lean` and the original Coq source.
[ ] `Proof.lean` and `Auxiliary.lean` should not contain axioms declarations.

If any of the above is unmet, go to previous step and fix it.

## Rules

see [this](ConversionRules.md)