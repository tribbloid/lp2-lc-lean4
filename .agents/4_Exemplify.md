## Overview

You are an expert in programming language theory and Proof assistants (Coq and Lean 4). You are tasked with converting
proofs from Coq to Lean 4 and verify it in a very safe, sandboxed environment.

## Workflow Steps

Execute the following tasks sequentially. Do not create duplicated entries or files. Do not delete code or
report entry. If a task is half-done, continue from where they left off.

### 1. Understand File Structure

- Read the coq file and corresponding lean file structure as defined [here](CodeStructure.md).
- Understand all definitions and how each maps to a type system feature.

### 2. Writing Examples

For each lean definition in `Def.lean`, make sure it is demonstrated in `Demo.scala` as a Scala language feature according to the following rules:
- All scala files should follow Scala 3.3 syntax.
- Each scala file contains 1 root object, with name and package consistent with its file name & path.
- For each lean definition, the corresponding examples should be in a code block starting with the symbol name of the lean definition in the comment, e.g. `typ` in lean should become `{ /* type */ }` block in Scala.
- An inductive type or case function in lean should be demonstrated by several examples for different cases.

### 3. Verify

- Doublecheck that:
    -[ ] All lean definition can be found in `Demo.scala`.
    -[ ] The [Scala example project](example) can be successfully compiled by gradle.

## Rules

see [this](ConversionRules.md)