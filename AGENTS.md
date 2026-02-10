## Project Overview

**lp2-lc-lean4** is a Lean 4 project to proof the soundness of various type theories. The project contains formal proofs
and definitions converted from Coq 8.4 to Lean 4.

The project depends on MathLib and AESOP

## Coding Rules

### General

#### Do

- Only ask questions during planning stage.
- Build after every revision, build early and often, prioritize correctness over progress.
- Eliminate compiler or LSP error as soon as possible.
- Theorem types must be concrete, do not use "True"/"False" as theorem type.
- Tool scripts not part of the core project should be placed in `.agent/script` directory.

#### Don't

- Do not ask questions like "what to do next", always follow the workflow by the numbers.
- Do not proceed to the next step if there is a pending compiling error.
- Do not create new branch in git.
- Do not write duplicated or redundant implementation.
- Do not remove comments.
- Do not write comments to explain intention.
- Do not add markdown files on your own.
- Do not change build file unless asked to.

### Structure

See [.agent/CodeStructure.md](.agent/CodeStructure.md)

### Lean Code Convention

#### Naming

- When creating a new Lean file, do not include `.` in the file name.
- Use snake_case for definitions and functions.
- Use PascalCase for types and structures, first letter capitalized.

#### Modules

- Import all lean files in module aggregator to be compiled by `lake build`.
- Use quoted module names: `import «Lp2lc».module`.
- Group imports logically (Lean core, external deps, local modules).

#### Conversion

See [.agent/ConversionRules.md](.agent/ConversionRules.md)

#### Quality Checks

- Lean files build successfully with `lake build`.
- [ ] All files compile without errors.
- [ ] No unused variable warnings.

## Key Commands

### Build & Check

- `lake build` - Build the entire project.
- `lake build <file path>` - Build one file.

### Development

- `lake clean` - Clean build artifacts.
- `lake update` - Update dependencies.
