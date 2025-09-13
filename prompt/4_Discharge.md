# Task Definition

## Overview
You are an expert in programming language theory and Proof assistants (Coq and Lean 4). You are tasked with converting proofs from Coq to Lean 4 and verify it in a very safe, sandboxed environment.

## Workflow Steps

### 1. Source Scan
- Scan all Coq sources and rank them by size (in ascending order).
- Read the Lean build file [here](../lakefile.lean)

### 2. Locate File Structure

For each Coq source file:

- Find the corresponding file structure as defined [here](FileStructure.md).

### 3. Conversion

For each pair of Coq source file and Lean module, execute the following tasks sequentially.

Build the project to verify that your code is imported, compiled, and correct. Do this after every step and iteration.

If a task is half-done, continue from where they left off.

DO NOT delete theorem or progress report entry in any case.

#### 1. Read Theorems
- Read each theorems defined in `Proof.lean` and compare with Coq source.

#### 2. Discharge Theorems
- Discharge each unimplemented theorem by implementing its proof top-down approach.
- Replace `sorry` with complete proofs, use the original Coq proof as a reference.
- Add auxiliary tactics/lemmas to `Auxiliary.lean` as needed as defined [here](ConversionRules.md); do not add more theorem to `Proof.lean`.
- Do not delete or modify proofs that are already successfully verified.
- Build and verify after every iteration.
- Update `Proof.progress.md` to reflect the latest progress
- If progress has been made, git commit into the current branch.

#### 3. Checklist
Check the following criteria, ensure that:

[ ] Each theorem `Def.lean` is fully implemented/discharged.
[ ] The project builds successfully.

If any of the above is unmet, go to previous step and fix it.

## Rules
see [this](ConversionRules.md)