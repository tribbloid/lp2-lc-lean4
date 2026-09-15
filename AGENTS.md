# AGENTS.md - Project Guide

## Project Overview

**lp2-lc-lean4** is a Lean 4 project to prove the soundness of various type theories. The project contains formal proofs and definitions in Lean 4.

The project depends on Aesop through Lake.

## Guardrails

### Do

- Build after every revision. Do not proceed while compiler/LSP errors remain; final Lean changes must pass `lake build` without errors. Existing `sorry`-backed scaffolds may remain only when the current task is not discharging them; do not introduce new production `sorry` unless the task is explicitly Conjecture Scaffolding.
- Only create new permanent core file if required by `.agent/CodeStructure.md`.
  - Agent tool scripts not part of the core project should be under `<project-dir>/.agent/script` directory.
  - Other new files should be under any "\__TEMP" subdirectory.

### Don't

- DO NOT ask questions like "what to do next".
- DO NOT repeat code! Avoid duplicated implementation and names; import namespaces/packages used multiple times.
- DO NOT change Lake/build config or toolchain files (`lakefile.lean`, `lake-manifest.json`, `lean-toolchain`) unless asked to.
- DO NOT revert any part of the code to a previous state in git history - every git commit is there for a reason
- DO NOT modify any code that is modified in the previous few commits and can compile successfully - they are the effective changes you need to adapt to

## Structure

See [.agent/CodeStructure.md](.agent/CodeStructure.md). Also follow the nearest nested `AGENTS.md`; examples such as Tests/AGENTS.md are not exhaustive.

## Lean Code Convention

### Guardrails

#### Do

- All non-trivial definition (longer than 3 lines) in syntax & semantic rules must be with a short docString explaining their necessity. This rule doesn't apply to test code, abbreviation, or explicitly educational tutorial/demo modules.
- Core proof and calculus modules should move executable checks to `Tests`. Tutorial/demo modules may contain `example`, `#eval`, `#check`, or `#rfl` commands when those commands are the point of the demonstration.
- All function/constructor arguments must be named at define-site, call-site names are not necessary.
- Do not repeated pattern-match conditions, they should be as short as possible
- Field namespace/class (namespace/class supporting an existing type, where functions inside can be invoked with dot-notation) have special rules:
  - If the namespace contain multiple functions, the namespace should be declared explicitly.
  - All functions under the namespace/class should be compatible with dot-notation, namely their first argument should be consistent.
  - All call-site should use dot-notation if possible (including test cases)
  - Avoid repetitive declaration of namespace unless it is to avoid forward reference in Lean.

#### Don't

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
- Do not put argument type after colon unless absolutely necessary

### Task-specific Guardrails

When working on a issue that contains multiple subtasks:

- Each subtask should be classified into one of the following Categories:
  - **Refactoring/Cleanup** is for enforcing code format & compliance without introduce meaningful change. DO NOT introduce or update type signature, definition, or proof (even if it is missing or `sorry`). Existing code structure should be preserved at all cost.
  - **Conjecturing** is for defining or revising proposition/type definitions (including those required to state the proposition).
    - Only add proof with "sorry" as placeholder
    - You must strive to write short abstraction, if your revision make the code longer, STOP IMMEDIATELY, commit your work, and ask for approval.
    - DO NOT add definitions that repeats implementations or cases, they should be in shared abstractions.
  - **Proving/Discharging/Refuting** is for proving existing proposition.
    - DO NOT remove or modify any type/proposition.
    - introducing new lemma is permitted if & only if they help proving the main theorem, but they have to be proven.
    - If a lemma or theorem is false/refutable, it should be recorded in DEFECTS.md with a counterexample in Tests directory.
    - In the end, no new `sorry` should be introduced.
  - **Example/Demo/Test/Benchmark** is for writing example & test case for existing definition in the Tests directory.
    - DO NOT write or update production code (unless it is a demo allowed by the Guardrails above).
    - Theorem//lemma are self-contained and erased at runtime, they require no example or test case.
- If one requested change would otherwise combine a **Conjecture Revision** with **Proving/Discharge**, always split it into two ordered subtasks and commits:
  1. First, make a **Conjecture Revision** commit containing only the proposition/type definitions and required statement-signature revisions. This scaffolding commit may temporarily fail to compile solely because its dependent proofs are stale.
  2. Second, make a **Proving/Discharge** commit containing the dependent proof revisions and restore a successful build.
- Each subtask should have its own independent git commit. When you complete one, commit immediately.

### Source Code Style

#### Modules

- Group imports logically (Lean core, external deps, local modules).

#### File Name

- `__` prefix in file name indicates experimental, self-contained code, non-experimental code should not import from it

#### Definitions

- Use camelCase for definitions and functions that yield values.
- Use camelCase for inductive cases/constructors
- Use PascalCase for types, propositions, properties, type constructors and predicates that yield `Type`/`Type u`/`Prop`/`Sort u`, first letter capitalized.

#### Omission

Some Lean symbols can be inferred by the compiler automatically and should be better left implicit:

- Full prefix of inductive case/constructor at call-site (a prefix of `.` is often enough)
- Type annotation of implicit argument at define-site (the argument variable however should never be omitted, even if it can be inferred)
- shared argument that is already defined in section variable header

#### Glossary/Abbreviations

- `T` prefix: type/sort argument (as in C#)
- `Ref` : reference
- `Gen`/`_` suffix : generator
- `Dep` prefix : dependent, related to dependent type
- `Rec` : recursive, guarded recursion

## Git (Version Control)

- Commit message always have the following format:

```
[{{LLM MODEL}}] {{Task Info}} {{Optional Subtask Category & Info}}
```

- If a task contains multiple subtasks:
  - each subtask should have its own commit.
  - after each commit:
    - launch a subagent to review it for guardrail compliance.
- If HEAD is DETACHED, create a temporary branch and commit into it
- If the commit can't compile cleanly, it should have [WIP] in its commit message

## Planning

- Any inconsistency or contradiction discovered during the planning stage must be immediately raised and highlighted in the plan
- no plan shall be executed until the inconsistency or contradiction is full addressed

## Key Commands

### Build & Check

- `lake build <file path>` - Build one file.

### Development

- `lake clean` - Clean build artifacts.
- `lake update` - Update dependencies.
