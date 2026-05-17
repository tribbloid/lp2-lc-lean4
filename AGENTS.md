## Project Overview

**lp2-lc-lean4** is a Lean 4 project to prove the soundness of various type theories. The project contains formal proofs and definitions in Lean 4.

The project depends on Aesop through Lake.

## Coding Rules

### General

#### Do

- Build after every revision. Do not proceed while compiler/LSP errors remain; final Lean changes must pass `lake build` without errors. Existing `sorry`-backed scaffolds may remain only when the current task is not discharging them; do not introduce new production `sorry` unless the task is explicitly Conjecture Scaffolding.
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

See [.agent/CodeStructure.md](.agent/CodeStructure.md). Also follow the nearest nested `AGENTS.md`; examples such as [Tests/AGENTS.md](Tests/AGENTS.md) are not exhaustive.

### Lean Code Convention

#### Guardrails

- Do not use `unsafe`, `noncomputable`, or `partial` declarations/blocks unless it is test or example code.
- Do not write axiom.
- All non-trivial definition (longer than 3 lines) in syntax & semantic rules must be with a short docString explaining their necessity. This rule doesn't apply to test code, abbreviation, or explicitly educational tutorial/demo modules.
- Tutorial/demo modules may contain `example`, `#eval`, `#check`, or `#rfl` commands when those commands are the point of the demonstration. Core proof and calculus modules should move executable checks to `Tests`.
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

#### Stages

Every task can be classified into one of the following stages:

- **Compliance Revision** is for making format & compliance revision. DO NOT introduce or update type signature, definition, or proof (even iff it is missing or `sorry`). Existing code structure should be preserved at all cost
- **Conjecture Scaffolding** is for introducing new `Prop`/Predicate, either as a type or as a theorem with `sorry`, DO NOT write any proof.
- **Example/Demo/Test** is for writing example & test case for existing definition in the Tests directory. DO NOT write or update production code except for explicitly educational tutorial/demo modules allowed by the Guardrails above. Theorem or lemma requires no example or test case.
- **Proof Discharge** is for proving existing conjecture/lemma/theorem, DO NOT write new `sorry`, introducing new lemma is permitted if & only if they help proving the main theorem, but they have to be proven immediately. If a lemma or theorem is believed to be false, a counterexample should be added into Tests directory.

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

- `lake build <file path>` - Build one file.

### Development

- `lake clean` - Clean build artifacts.
- `lake update` - Update dependencies.
