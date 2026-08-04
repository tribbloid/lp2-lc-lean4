## Project Overview

**lp2-lc-lean4** is a Lean 4 project to prove the soundness of various type theories. The project contains formal proofs and definitions in Lean 4.

The project depends on Aesop through Lake.

## Coding Rules

### Guardrails

#### Do

- Build after every revision. Do not proceed while compiler/LSP errors remain; final Lean changes must pass `lake build` without errors. Existing `sorry`-backed scaffolds may remain only when the current task is not discharging them; do not introduce new production `sorry` unless the task is explicitly Conjecture Scaffolding.
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

##### Do

- All non-trivial definition (longer than 3 lines) in syntax & semantic rules must be with a short docString explaining their necessity. This rule doesn't apply to test code, abbreviation, or explicitly educational tutorial/demo modules.
- Core proof and calculus modules should move executable checks to `Tests`. Tutorial/demo modules may contain `example`, `#eval`, `#check`, or `#rfl` commands when those commands are the point of the demonstration.
- All function/constructor arguments must be named at define-site, call-site names are not necessary.
- Do not repeated pattern-match conditions, they should be as short as possible
- Field namespace/class (namespace/class supporting an existing type, where functions inside can be invoked with dot-notation) have special rules:
  - If the namespace contain multiple functions, the namespace should be declared explicitly.
  - All functions under the namespace/class should be compatible with dot-notation, namely their first argument should be consistent.
  - All call-site should use dot-notation if possible (including test cases)
  - Avoid repetitive declaration of namespace unless it is to avoid forward reference in Lean.

##### Don't

- Do not remove or overwrite comment.
- Do not write code contradicting with the comment.
- Do not uncomment code or duplicate commented code.
- Do not add `unsafe`, `noncomputable`, or `partial` declarations/blocks.
- Do not introduce axiom without explicit request.
- Do not write multiple cases in pattern matching in 1 line; each case should be in its own line starting with `|`.
- Do not add compiler public API for already-defined feature (e.g. type-checking, evaluation). Each feature should only have 1 public definition.
- Do not use generic universe if possible, use static Prop/Type/Sort level on-demand (Type, Type 1, Type 2).
- Do not write trivial, short wrapper function: its body should be inlined.
- Do not export definition, only open at callsite.
- Do not write unnecessary argument at callsite.
- Do not create Lean file with `.` in file name.
- Do not use the following Lean keywords:
  - `forall` (use `∀`)
  - `exists` (use `∃`)
  - `fun` (use `λ`)
  - `show` (use simple type annotation)
  - `suffices` (use `have`)

#### Task-specific Guardrails

When working on a issue that contains multiple subtasks:
- Each subtask should have its own independent git commit. When you complete one, commit immediately.
- Each subtask should be classified into one of the following Categories:
  - **Refactoring/Cleanup** is for enforcing code format & compliance without introduce meaningful change. DO NOT introduce or update type signature, definition, or proof (even if it is missing or `sorry`). Existing code structure should be preserved at all cost.
  - **Conjecture Revision** is for defining or revising proposition/type definitions (including those required to state the proposition).
    - DO NOT write any proof.
    - You MUST use a subagent to review compliance to the above rule(s).
  - **Proving/Discharge** is for proving existing proposition.
    - DO NOT remove or modify any type/proposition.
    - introducing new lemma is permitted if & only if they help proving the main theorem, but they have to be proven.
    - If a lemma or theorem is believed to be false, a counterexample should be added into Tests directory.
    - In the end, no new `sorry` should be introduced.
    - You MUST use a subagent to review compliance to the above rule(s).
  - **Example/Demo/Test/Benchmark** is for writing example & test case for existing definition in the Tests directory.
    - DO NOT write or update production code (unless it is a demo allowed by the Guardrails above).
    - Theorem//lemma are self-contained and erased at runtime, they require no example or test case.

#### Source Code Style

##### Modules

- Use quoted module names, e.g. `import «Lp2lc».xxx`.
- Group imports logically (Lean core, external deps, local modules).

##### Definitions

- Use camelCase for definitions and functions that yield values.
- Use camelCase for inductive cases/constructors
- Use PascalCase for types, propositions, properties, type constructors and predicates that yield `Type`/`Type u`/`Prop`/`Sort u`, first letter capitalized.

##### References

- Inductive constructor at call-site should omit type name if possible, in this case, the constructor should always be preceded by `.`

##### Glossary/Abbreviations

- `T` prefix: type/sort argument (as in C#)
- `Ref` : reference
- `Gen` suffix : generator
- `Dep` prefix : dependent, related to dependent type
- `Rec` : recursive, guarded recursion
- `__` : experimental, self-contained code, non-experimental code should not import from it

## Key Commands

### Build & Check

- `lake build <file path>` - Build one file.

### Development

- `lake clean` - Clean build artifacts.
- `lake update` - Update dependencies.
