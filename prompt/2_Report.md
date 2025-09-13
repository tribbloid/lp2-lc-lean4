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

### 3. Report Progress

For each pair of Coq source file and Lean module, execute the following tasks sequentially.

#### 1. Enforce Code Structure
- Comment out all theorems in `Def.lean`
- Delete all axioms in `Proof.lean` and `Auxiliary.lean`

#### 2. Report Definitions
- Extract definitions, axioms, types from the Coq source.
- Compare them with conversion result in `Def.lean`.
- Summarize their status in `Def.progress.md`.

#### 3. Report Theorems
- Extract theorems, lemma and proofs from the Coq source.
- Compare them with conversion result in `Proof.lean`.
- Summarize their status in `Proof.progress.md`.

#### 4. Checklist
Check the following criteria, ensure that:

[ ] Each Coq declaration is tracked by `Def.progress.md` and `Proof.progress.md`?
[ ] Each Lean declaration is tracked by `Def.progress.md` and `Proof.progress.md`?

If any of the above is unmet, go to previous step and fix it.

## Rules

see [this](ConversionRules.md)