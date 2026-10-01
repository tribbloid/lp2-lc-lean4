# AGENTS.md - Project Guide

## Project Overview

**lp2-lc-lean4** is a Lean 4 project to prove the soundness of various type theories. It contains formal proofs
and definitions in Lean 4.

The project depends on Aesop through Lake.

## Guardrails

### Do

- Build after every revision. Do not proceed while compiler/LSP errors remain; final Lean changes must pass
      `lake build` without errors. Existing `sorry`-backed scaffolds may remain only when the current task is not
      discharging them; do not introduce new production `sorry` unless the task is explicitly Conjecture Scaffolding.
- Only create new permanent core file if required by `.agent/CodeStructure.md`.
    - Agent tool scripts not part of the core project should be under the `<project-dir>/.agent/script` directory.
    - Other new files should be under a `__TEMP` subdirectory.

### Don't

- DO NOT ask questions like "what to do next".
- DO NOT repeat code! Avoid duplicated implementation and names; import namespaces/packages used multiple times.
- DO NOT change Lake/build config or toolchain files (`lakefile.lean`, `lake-manifest.json`, `lean-toolchain`)
      unless asked to.
- DO NOT revert any part of the code to a previous state in git history; every commit is there for a reason.
- DO NOT modify any code that is modified in the previous few commits and can compile successfully; they are the
      effective changes you need to adapt to.
- DO NOT delete comment without an explicit reason.

## Structure

See [.agent/CodeStructure.md](.agent/CodeStructure.md). Also follow the nearest nested `AGENTS.md`; examples such
as [Tests/AGENTS.md](Tests/AGENTS.md) are not exhaustive.

## Lean Code Convention

### Guardrails

#### Do

- Core proof and calculus modules should move executable checks to `Tests`. Tutorial/demo modules may contain
      `example`, `#eval`, `#check`, or `#rfl` commands when those commands are the point of the demonstration.
- Function definitions (including type and case constructors) should:
    - Use binder/parameter style if applicable instead of arrow style.
    - Name all arguments.
- Do not repeat pattern-match conditions; keep them as short as possible.
- Multiple functions with the same namespace prefix should be grouped into as few explicit namespace blocks as
      possible.
- If multiple functions in a namespace block can be shortened with shared section variables, they should be.
- Shorten function calls with dot notation when possible.

#### Don't

- Do not add `unsafe`, `noncomputable`, or `partial` declarations/blocks.
- Do not introduce axioms without an explicit request.
- Do not write multiple cases in pattern matching in 1 line; each case should be in its own line starting with `|`.
- Do not add compiler public API for an already-defined feature (e.g. type-checking, evaluation). Each feature
      should have only one public definition.
- Avoid generic universes when a fixed `Prop`, `Type`, or `Sort` level suffices (`Type`, `Type 1`, `Type 2`).
- Do not write trivial, short wrapper function: its body should be inlined.
- Do not export definition, only open at callsite.
- Do not write unnecessary arguments at call sites.
- Do not create Lean file with `.` in file name.
- Do not use the following Lean keywords:
    - `forall` (use `∀`)
    - `exists` (use `∃`)
    - `fun` (use `λ`)
    - `show` (use simple type annotation)
    - `suffices` (use `have`)

### Task-specific Guardrails

When working on an issue that contains multiple subtasks:

- Each subtask should have its own independent git commit. When you complete one, commit immediately.
- Typo or underspecified part in documentation/comment should be corrected and committed before actual work start.
- Each subtask should be classified into one of the following categories:
    - **Refactoring/Cleanup** enforces code format and compliance without meaningful changes. DO NOT introduce
      or update type signatures, definitions, or proofs (even if missing or `sorry`). Preserve the existing
      code structure.
    - **Conjecturing** defines or revises proposition/type definitions, including those needed to state a
      proposition.
        - Only add proofs with `sorry` as a placeholder.
        - Strive for shorter abstractions. If a revision makes code longer (not comment), STOP IMMEDIATELY, commit the
          code, and ask for approval.
        - DO NOT add definitions that repeat implementations or cases; use shared abstractions.
    - **Proving/Discharging/Refuting** proves an existing proposition.
        - DO NOT remove or modify any type or proposition.
        - Introduce new lemmas only if they help prove the main theorem.
        - Before proving, launch subagent(s) to try to refute the theorem by writing a refutation in `Tests`
          and explaining it in `DEFECT.md`:
            - The set of axioms is inconsistent and can be used to construct `False`.
            - The theorem has a counterexample.
        - Introduce no new `sorry` in the final proof.
    - **Example/Demo/Test/Benchmark** writes examples or tests for existing definitions in `Tests`.
        - DO NOT write or update production code unless it is a demo allowed by the guardrails above.
        - Theorems and lemmas are self-contained and erased at runtime; they need no test cases.
- If one requested change would otherwise combine a **Conjecture Revision** with **Proving/Discharge**, always
      split it into two ordered subtasks and commits:
    1. First, make a **Conjecture Revision** commit containing only the proposition/type definitions and required
      statement-signature revisions. This scaffolding commit may temporarily fail to compile solely because
      its dependent proofs are stale.
    2. Second, make a **Proving/Discharge** commit containing the dependent proof revisions and restore a
      successful build.

### Source Code Style

#### Modules

- Group imports logically (Lean core, external deps, local modules).

#### File Name

- The `__` file prefix indicates experimental, self-contained code; non-experimental code should not import it.

#### Definitions

- Use camelCase for definitions and functions that yield values.
- Use camelCase for inductive cases and constructors.
- Use PascalCase for types, propositions, properties, type constructors, and predicates that yield
      `Type`/`Type u`/`Prop`/`Sort u`.

#### Omission

Some Lean symbols can be inferred by the compiler automatically and should be better left implicit:

- Full prefix of inductive cases or constructors at call sites (a prefix of `.` is often enough).
- Type annotation of implicit arguments at the definition site (the argument variable should never be omitted,
      even if its type can be inferred).
- Shared arguments already defined in a section variable header.

#### Glossary/Abbreviations

- `T` prefix: type/sort argument (as in C#).
- `Ref`: reference.
- `Gen`/`_` suffix: generator.
- `Dep` prefix: dependent, related to a dependent type.
- `Rec`: recursive, guarded recursion.

## Documentation (including Markdown & Comments)

Before starting to work on code, actively enforce the following guardrails on every document you read; apply
corrections in one or more preceding git commits if necessary:

- Indentation is 4 spaces, continuation indentation is 6 spaces.
- Hard wrap is 120 characters. The only exceptions are table and markup sections
      which can be longer.
- Duplicated or contradicting information should be merged or deleted.
- Inconsistent or dangling references should be fixed.
- Spelling and syntax errors should be fixed.
- All references must point to existing code or artefacts; references to historical
      objects must be deleted.

## Git (Version Control)

- Commit messages always have the following format:

```
[{{LLM MODEL}}] {{Task Info}} {{Optional Subtask Category & Info}}
```

- If a task contains multiple subtasks:
    - each subtask should have its own commit.
    - after each commit:
        - launch a subagent to review it for guardrail compliance.
- If HEAD is detached, create a temporary branch and commit into it.
- If the commit can't compile cleanly, include `[WIP]` in its message.

## Planning

- Any inconsistency or contradiction discovered during the planning stage must be immediately raised and
      highlighted in the plan.
- No plan shall be executed until the inconsistency or contradiction is fully addressed.

## Key Commands

### Build & Check

- `lake build <file path>` - Build one file.

### Development

- `lake clean` - Clean build artifacts.
- `lake update` - Update dependencies.
