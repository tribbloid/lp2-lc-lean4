# Conversion Task Definition

## Overview
You are an expert in PL theory and Proof assistants (Coq and Lean 4), you are tasked with converting Coq code to Lean 4 code and compile/verify in a very safe, sandboxed environment.

## Workflow Steps
You should do the following tasks by the numbers:

### 1. File Structure Setup
- Create target directory if not exists: `Lp2lc_coq/path/<name>.v` → `Lp2lc/path/<name>/`
- Generate three files if not exists:
   1. `Def.lean`: definitions and axioms.
   2. `Proof.lean`: theorems and proofs (including proof scaffolds)
   3. `Auxiliary.lean`: auxiliary tactics and lemma to support the original proofs
- DO NOT write into any other files

### 2. Definition Conversion
- Extract all definitions, axioms, types from Coq source
- Convert to Lean 4 syntax following conversion rules
- Write to `Def.lean` with original line number comments
- Build and verify after each definition

### 3. Proof Scaffolding
- Extract all theorems and lemmas from Coq source
- Create theorem statements with `sorry` proof bodies in `Proof.lean`
- Maintain original declaration order
- git commit into the current branch after this step is complete

### 4. Proof Implementation
- Discharge & implement proofs top-down approach
- Replace `sorry` with complete proofs
- Add auxiliary tactics/lemmas to `Auxiliary.lean` as needed
- Build and verify after every change
- if you made progress by successfully verifying a new proof, update `report.md` (with numbers in the overview) to summarize your progress, then git commit into the current branch
- do not delete proofs that are already successfully verified

Repeat step 4 until all proofs are discharged and verified. Do not ask for permission.

## Conversion Rules
- Preserve original names (add `def_` prefix only if required by Lean syntax) and orders
- Prefix each declaration with a comment indicating original Coq line number (strictly incremental)
- use "sorry" with "TODO" comment for incomplete proofs
- `Set`/`Prop` → Lean `Prop`
- `Type` → Lean `Prop` (avoid `Type` unless necessary)
- `Var` from LibLN → Lean structure with `String` field
- `Hint Constructors` → `@[aesop constructor]` attribute on type constructor
- `Hint Resolve` → `@[aesop]` attribute on function (create wrapper functions if needed)
- `Lemma` → `Theorem`
- `Tactic Notation` → Lean tactic macro with examples
- `Ltac` → Lean elaborator with examples
- `LibEnv` lemma reference `ok E` → a minimal abstract `ok : env → Prop` in `Aux.lean` to keep statements typechecking

## Quality Checks
- [ ] All files compile without errors
- [ ] No unused variable warnings
- [ ] Line number references accurate
- [ ] All theorems proven or marked with TODO
- [ ] Aesop attributes properly applied

## Success Criteria
- Complete 1:1 conversion of all declarations
- Lean files build successfully with `lake build`
- Proofs verified or explicitly marked as incomplete
