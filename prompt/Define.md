# Task Definition

## Overview

You are an expert in programming language theory and Proof assistants (Coq and Lean 4). You are tasked with converting
proofs from Coq to Lean 4 and verify it in a very safe, sandboxed environment.

## Workflow Steps

### 1. Source Scan

- Scan all Coq sources and rank them by size (in ascending order).
- Read the Lean build file [here](../lakefile.lean)

### 2. File Structure Setup

For each Coq source file:

- Create (if not exists) the corresponding file structure as defined in [this](FileStructure.md), including Lean directory/modules, module aggregators, markdown reports and sections.
- Do not delete existing file or directory.
- Do not remove any file contents.

### 3. Planning

For each pair of Coq source file and Lean module:

- Verify the file structure and sections created in step 2.
- Update `progress.md` files in the Lean directory as defined in [this](FileStructure.md) to reflect conversion progress.
    - Read definitions, axioms, types from the Coq source and compare with `Def.lean`, report in `Def.progress.md`.
    - Read theorems, lemma and proofs from the Coq source and compare with `Proof.lean`, report in `Proof.progress.md`.
- Ask for clarification if necessary.

### 4. Conversion

For each pair of Coq source file and Lean module, execute the following tasks sequentially.

Build the project to verify that your code is imported, compiled, and correct. Do this after every step and iteration.

If a task is half-done, continue from where they left off.

#### 1. Definition Conversion
- Extract all definitions, axioms, types from Coq source.
- Convert to Lean 4 syntax following conversion rules.
- Write to `Def.lean` with original line number comments.
- Update `Def.progress.md` to reflect your progress.

#### 2. Proof Scaffolding
- Extract all theorems and lemmas from Coq source.
- Create theorem statements with `sorry` proof bodies in `Proof.lean`.
- Update `Proof.progress.md` to reflect your progress.
- DO NOT try to discharge the proofs.
- Maintain original declaration order.
- Git commit into the current branch after this step is complete.

#### 3. Verification
- Verify the progress in `Def.progress.md` and `Proof.progress.md` by comparing with the Lean source.
- For any Coq definition or proof that is not converted to Lean, continue the conversion from where they differs.

### 3. Aggregation
- Finally, Check if all Coq source files have been converted into corresponding Lean modules.

## Rules

see [this](ConversionRules.md)