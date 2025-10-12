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

#### 2. Explain Theorems

- Ensure that each theorem in coq or lean file is explained in `Glossary.md`.
- The explanation should be clear and concise, and contains at least its term/symbol name (as used in the code), its
  full name, and its meaning/purpose.
- If the subject is a primary conclusive theorem and not a lemma, you should also explain why it entails the soundness
  of the type system.
- Doublecheck that:
    -[ ] All theorem in coq file is included in `Glossary.md`.
    -[ ] All theorem in lean file is included in `Glossary.md`.

## Rules

see [this](ConversionRules.md)