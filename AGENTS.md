# AGENTS.md - Project Guide

## Project Overview

**lp2-lc-lean4** is a Lean 4 project to prove the soundness of various type theories. It contains formal proofs and
definitions in Lean 4.

The project depends on Aesop through Lake.

## Guardrails/Rules

They may exist in various texts (generally starting with "Rule:" or "Rules:"), each defines a contract for a task or
subtask that shall not be violated:

- "AGENTS.md" files
- code comment
- prompts & instructions

A subagent MUST be launched at the end of each task or subtask to obstruct any violation. The reviewer must independently
read applicable rules and inspect the complete task diff, including tests and helpers, without adopting the author's
assessment.

- Report **PASS**, **FAIL**, or **UNRESOLVED** for each applicable rule, with the rule text and concrete diff evidence.
      A passing build does not establish compliance with other rules.
- For every code-size restriction, record its scope and starting revision. Measure code characters excluding comments
      and whitespace, and nonblank code lines, before and after, per file and across the complete affected code.
      Growth in either metric within the restricted scope triggers the growth rule; fewer lines cannot excuse more
      characters. Include required tests and helpers; do not compress formatting or relocate code to evade the limit.
- Explicitly check the necessity and duplication of added tests, fixtures, and proof boilerplate as well as production
      code. Repeated checks must be shared or removed.
- **FAIL** and **UNRESOLVED**, including qualified reviewer warnings, block dependent work and compliance claims.
      Resolve them with a correction and renewed review, or obtain human approval where the applicable rule requires it.
      The author cannot dismiss a finding by choosing a more favorable size metric.

### Do

- Build after every revision. Do not proceed while compiler/LSP errors remain; final Lean changes must pass `lake build`
      without errors. Existing `sorry`-backed scaffolds may remain only when the current task is not discharging them;
      do not introduce new production `sorry` unless the task is explicitly Conjecture Scaffolding.
- Create a new permanent file only when the user explicitly authorizes its creation and `.agent/CodeStructure.md`
      permits it. A request to fix or extend existing code does not authorize new files.
    - Reuse existing files for tests, fixtures, helpers, and shared utilities. Deduplication, convenience, and reviewer
          recommendations do not authorize creating a file.
    - If the task cannot be completed within existing files, explain the proposed file's path and purpose and obtain
          explicit user approval before creating it. Do not create or commit it while approval is pending.
    - Agent tool scripts not part of the core project should be under the `<project-dir>/.agent/script` directory.
    - Temporary files (e.g. experiments and demos) should be under a `__TEMP` subdirectory.

### Don't

- DO NOT ask questions like "what to do next".
- DO NOT repeat code! Avoid duplicated implementation and names; import namespaces/packages used multiple times.
- DO NOT change Lake/build config or toolchain files (`lakefile.lean`, `lake-manifest.json`, `lean-toolchain`) unless
      asked to.
- DO NOT revert any part of the code to a previous state in git history; every commit is there for a reason.
- DO NOT modify any code that is modified in the previous few commits and can compile successfully; they are the
      effective changes you need to adapt to.
- DO NOT delete comment without an explicit reason, unless it is for obsolete TODO entry.

## Structure

See [.agent/CodeStructure.md](.agent/CodeStructure.md). Also follow the nearest nested `AGENTS.md`; examples such as
Tests/AGENTS.md are not exhaustive.

- Existing style and designated examples or style guides govern **all code structures**, including directory layout,
      file names (prefixes and suffixes), module boundaries and aggregators, namespace names and nesting, declaration
      placement and order, naming conventions, and public API organization. Follow the corresponding existing patterns;
      do not invent alternative structures, file naming conventions, or namespace hierarchies. Adapt names and content
      only as required by the requested task.

## Lean Code Convention

### Guardrails

#### Do

- Core proof and calculus modules should move executable checks to `Tests`. Tutorial/demo modules may contain `example`,
      `#eval`, `#check`, or `#rfl` commands when those commands are the point of the demonstration.
- Function definitions (including type and case constructors) should:
    - Use binder/parameter style if applicable instead of arrow style.
    - Name all arguments.
- Multiple functions with the same namespace prefix should be grouped into as few explicit namespace blocks as possible.
- If multiple functions in a namespace block can be shortened with shared section variables, they should be.
- Shorten function calls with dot notation when possible.
- Inline trivial functions or wrappers that are used only once.
- Every implicit coercion should be wrapping an explicit conversion method callable as dot-notation with no parameter.
- If an implicit coercion caused a compilation error, use the underlying explicit conversion method instead.
- Every permanent (non-temporary) Lean file must be mentioned in its module aggregator with either:
    - an import clause (`import XXX`), or
    - an import comment (`-- import XXX`).

#### Don't

- Do not add `unsafe` or `partial` declarations/blocks without an explicit request.
- Do not introduce axioms without an explicit request.
- Do not repeat match conditions; group them into simple tiers (particularly for induction fuel).
- Do not write multiple cases in inductive/match in 1 line; each case should be in its own line
      starting with `|`.
- Do not add compiler public API for an already-defined feature (e.g. type-checking, evaluation).
      Each feature should have only one public definition.
- Do not overuse generic universes when fixed levels suffice (`Prop`, `Type`, `Type 1`, `Type 2`).
- Do not export definition, only open at callsite.
- Do not write unnecessary arguments at call sites.
- Do not create Lean file with `.` in file name.
- Do not import temporary Lean files in a module aggregator.
- Do not import or modify Lean files in ".obsolete" directory.
- Do not.`open` a namespace if it is defined in the same file.
- Do not use the following Lean keywords:
    - `forall` (use `∀`)
    - `exists` (use `∃`)
    - `fun` (use `λ`)
    - `show` (use simple type annotation)
    - `suffices` (use `have`)

### Task-specific Guardrails

When working on an issue that contains multiple subtasks:

- Each subtask should have its own independent git commit. When you complete one, commit immediately.
- Each subtask should be classified into one of the following categories:

    - **Refactoring/Cleanup** enforces code format and compliance without meaningful changes. DO NOT introduce or update
      type signatures, definitions, or proofs (even if missing or `sorry`). Preserve the existing code structure.
    - **Conjecturing** introduces or revises definition, proposition and algorithm.
        - DO NOT:
            - make old algorithm much longer.
            - repeat (write the same concept twice or more) in schema definition, inductive/match case or algorithm implementation.
            - proof anything, all introduced theorem should be assigned `sorry`
            - if any of the above is absolutely necessary, commit your work, then STOP IMMEDIATELY and ask for human approval.
        - Prefer laconic, succinct code.
        - Prefer predefined shared concept & abstraction.
    - **Proving/Discharging/Refuting** proves an existing proposition.
        - DO NOT remove or modify type of main, public theorems (AKA propositions).
        - Introduce relevant lemma (reusable private theorem) on-demand, but new lemma should always be documented for
          their motivation/intention.
        - Delete old lemma that are no longer useful or relevant.
        - Before proving the theorem, use subagent(s) to hunt for definitional defect(s) and log them in `DEFECT.md`:
            - vacuous, tautological, or trivial theorem/conjecture.
            - false conjecture with clear counterexample(s).
            - inconsistent/contradicting axioms & conditions that can be used to construct `False`.
    - **Example/Demo/Test/Benchmark** writes examples or tests for existing definitions in `Tests`.
        - DO NOT write or update production code unless it is a demo allowed by the guardrails above.
        - Theorems and lemmas are self-contained and erased at runtime; they need no test cases.
- If one requested change would otherwise combine a **Conjecture Revision** with **Proving/Discharge**, always split it
  into two ordered subtasks and commits:
  1. First, make a **Conjecture Revision** commit containing only the proposition/type definitions and required
     statement-signature revisions. This scaffolding commit may temporarily fail to compile solely because its
     dependent proofs are stale.
  2. Second, make a **Proving/Discharge** commit containing the dependent proof revisions and restore a successful build.

### Source Code Style

#### Modules

- Group imports logically (Lean core, external deps, local modules).

#### File Name

- The `__` file prefix indicates experimental, self-contained code; no other files should import from it (except other
 experimental files that share the same name prefix).

#### Definitions

- Use camelCase for terms inhabiting `Type 0` or below (e.g. value, function, proposition, predicate, proof)
- Use camelCase for case and constructor.
- Use PascalCase for terms inhabiting `Type 1` or above (e.g. type, type constructor, sort).

#### Omission

Some Lean symbols can be inferred by the compiler automatically and should be better left implicit:

- Full prefix of inductive cases or constructors at call sites (a prefix of `.` is often enough).
- Type annotation of implicit arguments at the definition site (the argument variable should never be omitted, even if
      its type can be inferred).
- Shared arguments already defined in a section variable header.

#### Glossary/Abbreviations

- `T` prefix: type/sort argument (as in C#).
- `Ref`: reference.
- `Gen`/`_` suffix: generator.
- `Dep` prefix: dependent, related to a dependent type.
- `Rec`: recursive, guarded recursion.

## Documentation (including Markdown & Comments)

Before starting to work on code, actively enforce the following guardrails on every document you read; apply corrections
in one or more preceding git commits if necessary:

- format is defined and enforced by @.markdownlint.jsonc and @dev/make-all.sh
- Duplicated or contradicting information should be merged or deleted.
- Correct the following defects in a new git commit before actual work start:
    - Typo/spelling error & syntax error.
    - Inconsistent or dangling reference.
    - Underspecified description & requirement.
- All references must point to existing code or artefacts; references to historical objects must be deleted.

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
- Do not read files in other worktree or diverging branch.

## Planning

- Any inconsistency or contradiction discovered during the planning stage must be immediately raised and highlighted in
      the plan.
- No plan shall be executed until the inconsistency or contradiction is fully addressed.

## Key Commands

### Build & Check

- `lake build <file path>` - Build one file.

### Development

- `lake clean` - Clean build artifacts.
- `lake update` - Update dependencies.
