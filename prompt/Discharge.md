# Task Definition

## Overview
You are an expert in programming language theory and Proof assistants (Coq and Lean 4). You are tasked with converting proofs from Coq to Lean 4 and verify it in a very safe, sandboxed environment.

## Workflow Steps

### 1. Source Scan

- Scan all Coq sources and rank them by size (in ascending order).
- Read the Lean build file [here](../lakefile.lean)

### 2. Conversion

For each Coq source file, execute the following tasks sequentially.

Build the project to verify that your code is imported, compiled, and correct. Do this after every step and iteration.

If a task is half-done, continue from where they left off.

#### 1. Read theorems
- Read the corresponding Lean module, progress reports and `specs.md` as defined in [this](FileStructure.md)
- Do not delete existing file or directory.
- Ask for clarification if necessary.

#### 2. Discharge Theorems
- Discharge each theorem by implementing its proof top-down approach.
- Replace `sorry` with complete proofs, use the original Coq proof as a reference.
- Add auxiliary tactics/lemmas to `Auxiliary.lean` as needed; do not add more theorem to `Proof.lean`.
- Do not delete or modify proofs that are already successfully verified.
- Build and verify after every iteration.
- Update `Proof.progress.md` to reflect the latest progress
- If progress has been made, git commit into the current branch.

#### 3. Verification
- Verify `Proof.progress.md` by comparing the list of theorems with the Lean source.
- Repeat `2. Discharge Theorems` step until all proofs are discharged and verified.
- Do not ask for permission until you reach a milestone.

## Rules
see [this](ConversionRules.md)