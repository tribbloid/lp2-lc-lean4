## Project Overview

**lp2-lc-lean4** is a Lean 4 project to proof the soundness of various type theories. The project contains formal proofs and definitions converted from Coq 8.4 to Lean 4

The project depends on Mathlib and AESOP

## Key Commands

### Build & Check
- `lake build` - Build the entire project
- `lake build <file path>` - Build one file

### Development
- `lake clean` - Clean build artifacts
- `lake update` - Update dependencies

## Workflow
- write 1 definition at a time, starting from top to bottom
- compile often to make sure that your definition and proof has no error
- if you cannot complete a proof, close it with "sorry" as a placeholder and move to other proofs, then come back later
- only introduce new dependency after my approval

## Code Conventions

### General
- Your code should be minimal and elegant
- eliminate compiler or LSP warning as soon as possible, particularly unused variable warnings
- when creating new Lean file, do not include `.` in file name
- do not write duplicated or redundant implementation
- Do not write comment unless is a line number
- do not remove comment

### Naming
- Use snake_case for definitions and functions
- Use PascalCase for types and structures

### Import Style
- Use quoted module names: `import «Lp2lc».module`
- Group imports logically (Lean core, external deps, local modules)

### Conversion Rules
- Converted Lean code should be in Lp2lc directory, with file name and directory structure similar to its corresponding Coq file, e.g. `Lp2lc_coq/active/agents.v` should be converted into `Lp2lc/active/agent.lean`
- Lean file should have the same name and relative path as the corresponding Coq file, e.g. `Lp2lc/agents/agents.lean`
- Lean definition (variable, function, type, prop, lemma, theorem, tactic) and corresponding Coq definition should have identical names, add prefix `def_` if necessary
- Lean definition and corresponding Coq definition should have the same order
- Lean definition should each have a comment of line number pointing to the corresponding Coq definition, these line numbers should be strictly incremental
- Coq `Set` and `Prop` should be converted to a Lean `Prop`
- Coq `Type` should also be converted to a Lean `Prop`, avoid declaring Lean `Type` unless necessary
- Coq `Var` in `LibLN` should be converted to a Lean structure type with `name : String` as the only member
- Coq `Hint Constructors` should be converted to a Lean aesop constructor attribute annotating the relevant type constructor
- Coq `Hint Resolve` and other kinds of `Hint` should be converted to a Lean aesop attribute annotating a function. It should be noted that Lean attribute cannot annotate an inductive case, so new function may need to be created to handle the case
- Coq `Lemma` should be converted to Lean `Theorem`
- Coq `Tactic Notation` should be converted to Lean tactic macro, input and output of the macro should be logged, followed by an example demonstrating its use case
- Coq `Ltac` should be converted to Lean elaborator, input and output of the macro should be logged, followed by an example demonstrating its use case

