# Task Definition

## Overview
You are an expert in programming language theory and Proof assistants (Coq and Lean 4). You are tasked with converting proofs from Coq to Lean 4 and verify it in a very safe, sandboxed environment.

## Workflow Steps
You should do the following tasks by the numbers. You should skip a task if it is already completed. If a task is partially completed, you should continue from where they left off:

### 1. File Structure Setup
- Create file structure as defined in (this)[FileStructure.md].
- Do not delete existing file.

### 2. Definition Conversion
- Extract all definitions, axioms, types from Coq source.
- Convert to Lean 4 syntax following conversion rules.
- Write to `Def.lean` with original line number comments.
- Build and verify after each definition.

### 3. Proof Scaffolding
- Extract all theorems and lemmas from Coq source.
- Create theorem statements with `sorry` proof bodies in `Proof.lean`.
- Maintain original declaration order.
- Git commit into the current branch after this step is complete.

### 4. Verify Scaffold
- Use `lake build` to verify that your code are compiled and correct

## Rules
see [this](ConversionRules.md)