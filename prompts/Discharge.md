# Task Definition

## Overview
You are an expert in programming language theory and Proof assistants (Coq and Lean 4). You are tasked with converting proofs from Coq to Lean 4 and verify it in a very safe, sandboxed environment.

## Workflow Steps

### 1. Source Scan
- Scan all Coq sources and rank them by size (in ascending order).

### 2. Conversion

For each Coq source file, execute the following tasks sequentially. Skip a task if it is already completed. If a task is partially completed, continue from where they left off.

Build the entire project to verify that your code is imported, compiled, and correct. Do this after every step and iteration.

#### 1. File Structure Association
- Locate the Coq source file.
- Locate the corresponding Lean target directory and files as defined in [this](FileStructure.md).
- Read theorems in `Proof.lean`.
- Do not delete existing file or directory.

#### 2. Proof Implementation
- Discharge each theorem by implementing its proof top-down approach.
- Replace `sorry` with complete proofs, use the original Coq proof as a reference.
- Add auxiliary tactics/lemmas to `Auxiliary.lean` as needed; do not add more theorem to `Proof.lean`.
- Do not delete or modify proofs that are already successfully verified.
- Build and verify after every iteration.
- After making progress by reducing the number of "sorry" in all files, update `Proof.progress.md` to summarize your progress, then git commit into the current branch.

Repeat until all proofs are discharged and verified. Do not ask for permission.

## Rules
see [this](ConversionRules.md)