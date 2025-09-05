## Project Overview

**lp2-lc-lean4** is a Lean 4 project to proof the soundness of various type theories. The project contains formal proofs and definitions converted from Coq 8.4 to Lean 4

The project depends on Mathlib and AESOP

## Planning Rules
- Always save your plan and TODO list as a new markdown file in `plans` directory.

## Coding Rules

### General
- DO NOT FUCKING ASK QUESTION! JUST FUCKING DO IT!
- Your code should be minimal and elegant
- eliminate compiler or LSP error/warning as soon as possible, particularly unused variable warnings
- do not proceed to the next step if there is pending compiling error
- when creating new Lean file, do not include `.` in file name
- do not write duplicated or redundant implementation
- do not remove comment
- Do not write comment to explain intention
- Do not add markdown file on your own

### Naming
- Use snake_case for definitions and functions
- Use PascalCase for types and structures

### Import Style
- Use quoted module names: `import «Lp2lc».module`
- Group imports logically (Lean core, external deps, local modules)

## Quality Checks
- Lean files build successfully with `lake build`.
- [ ] All files compile without errors or warning.
- [ ] No unused variable warnings.
- [ ] All theorems proven or marked with TODO.

## Key Commands

### Build & Check
- `lake build` - Build the entire project
- `lake build <file path>` - Build one file

### Development
- `lake clean` - Clean build artifacts
- `lake update` - Update dependencies
