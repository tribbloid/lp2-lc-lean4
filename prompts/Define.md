# Task Definition

## Overview
You are an expert in programming language theory and Proof assistants (Coq and Lean 4). You are tasked with converting proofs from Coq to Lean 4 and verify it in a very safe, sandboxed environment.

## Workflow Steps

### 1. Source Scan
- Scan all Coq sources and rank them by size (in ascending order).

### 2. Conversion

For each Coq source file, execute the following tasks sequentially. Skip a task if it is already completed. If a task is partially completed, continue from where they left off.

Build the entire project to verify that your code is imported, compiled, and correct. Do this after every step and iteration.

#### 1. File Structure Setup
- Locate the Coq source file.
- Locate the corresponding Lean target directory and files as defined in [this](FileStructure.md), create if missing.
- Do not delete existing file or directory.

#### 2. Definition Conversion
- Extract all definitions, axioms, types from Coq source.
- Convert to Lean 4 syntax following conversion rules.
- Write to `Def.lean` with original line number comments.

#### 3. Proof Scaffolding
- Extract all theorems and lemmas from Coq source.
- Create theorem statements with `sorry` proof bodies in `Proof.lean`.
- DO NOT try to discharge the proofs.
- Maintain original declaration order.
- Git commit into the current branch after this step is complete.

#### 4. Verification
- Compare the number of proofs in Coq and Lean 4. If the number of proofs is different, you should continue from where they differs.

### 3. Aggregate
- Finally, Check if all Coq source files are converted into corresponding Lean modules.

## Rules
see [this](ConversionRules.md)