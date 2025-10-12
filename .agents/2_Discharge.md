# Task Definition

## Overview

You are an expert in programming language theory and Proof assistants (Coq and Lean 4). You are tasked with converting
proofs from Coq to Lean 4 and verify it in a very safe, sandboxed environment.

## Workflow Steps

Execute the following tasks sequentially. Do not create duplicated entries or files. Do not delete theorem or progress
report entry. If a task is half-done, continue from where they left off.

### 1. Understand File Structure

- Read the coq file and corresponding lean file structure as defined [here](CodeStructure.md).
- Understand all theorems and their relationship.

#### 2. Discharge Theorems

- Discharge each unimplemented theorem by implementing its proof top-down approach.
- Replace `sorry` with complete proofs, use the original Coq proof as a reference.
- Add auxiliary tactics/lemmas to `Auxiliary.lean` as needed as defined [here](ConversionRules.md); do not add more
  theorem to `Proof.lean`.
- Do not delete or modify proofs that are already successfully verified.
- Build and verify after every iteration.
- Update `Proof.progress.md` to reflect the latest progress
- If progress has been made, git commit into the current branch.
- Doublecheck that:
    -[ ] Each lean theorem is fully implemented/discharged.
    -[ ] The project builds successfully.

## Rules

see [this](ConversionRules.md)