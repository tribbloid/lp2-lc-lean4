## Project Overview

**lp2-lc-lean4** is a Lean 4 project to prove the soundness of various type theories. The project contains formal proofs and definitions in Lean 4.

The project depends on Aesop through Lake.

## Coding Rules

### General

#### Do

- Build after every revision. Do not proceed while compiler/LSP errors remain; final Lean changes must pass `lake build` without unused-variable warnings.
- Theorem types must be concrete, do not use "True"/"False" as theorem type.
- Only create new permanent core file if required by `.agent/CodeStructure.md`.
  - Agent tool scripts not part of the core project should be under `<project-dir>/.agent/script` directory.
  - Other new files should be under any "__TEMP" subdirectory.

#### Don't

- Do not ask questions like "what to do next".
- Avoid duplicated implementation and repeated fully qualified names; import namespaces/packages used multiple times.
- Do not create new branch in git.
- Preserve existing comments. Do not add explanatory comments unless required by Lean docString policy.
- Do not change Lake/build config or toolchain files (`lakefile.lean`, `lake-manifest.json`, `lean-toolchain`) unless asked to.

### Structure

See [.agent/CodeStructure.md](.agent/CodeStructure.md). Also follow the nearest nested `AGENTS.md`, e.g. [Tests/AGENTS.md](Tests/AGENTS.md).

### Lean Code Convention

#### Guardrails

- Do not use `unsafe`, `noncomputable`, or `partial` declarations/blocks unless it is test or example code.
- Do not write axiom.
- All non-trivial definition (longer than 3 lines) in syntax & semantic rules must be with a short docString explaining their necessity. This rule doesn't apply to test code or abbreviation.
- All function/constructor arguments must be named at define-site, call-site names are not necessary.
- Multiple cases in pattern matching should never be in 1 line, each line should start with `|`.
- For repeated pattern-match conditions, prefer layered pattern matching.
- Avoid leaky abstraction: top-level public APIs should only contain interpreter/compiler API (e.g. type-checking, evaluation).
- Avoid generic universe if possible, use static Prop/Type/Sort level on-demand (Type, Type 1, Type 2)
- Field namespace/class (namespace/class supporting an existing type, where functions inside can be invoked with dot-notation) have special rules:
  - each namespace/class should only appear once.
  - if the namespace contain multiple functions, the namespace should be declared explicitly.
  - all functions under the namespace/class should be compatible with dot-notation, namely their first argument should be consistent.
  - all call-site should use dot-notation if possible (including test cases)

#### Naming

- When creating a new Lean file, do not include `.` in the file name.
- Use camelCase for definitions and functions that yield values.
- Use PascalCase for types, propositions, properties, type constructors and predicates that yield `Type`/`Type u`/`Prop`/`Sort u`, first letter capitalized.
- Variable name of `Prop` or `Bool` type should contain "is"/"Is" 

#### Modules

- Use quoted module names, e.g. `import «Lp2lc».xxx`.
- Group imports logically (Lean core, external deps, local modules).

## Key Commands

### Build & Check

- `lake build` - Build the entire project.
- `lake build <file path>` - Build one file.

### Development

- `lake clean` - Clean build artifacts.
- `lake update` - Update dependencies.
