# AGENTS.md

This file provides guidance for AI agents working on the lp2-lc-lean4 project, which focuses on System-F with subtyping implementations in Lean 4, converted from Rocq (Coq).

## Project Overview

**lp2-lc-lean4** is a Lean 4 implementation of System-F with subtyping, exploring type theory concepts and demonstrating the motto "who needs type constructor? (in lean 4)". The project converts formal proofs and definitions from Rocq/Coq to Lean 4.

## Key Commands

### Build & Check
- `lake build` - Build the entire project
- `lake exe lp2lc` - Run the main executable
- `lean --check` - Check syntax and types

### Development
- `lake clean` - Clean build artifacts
- `lake update` - Update dependencies

## Project Structure

### Core Directory: `Lp2lc/`

- **`Active.lean`** - Main active imports (currently imports from Claude4/ and active/)
- **`Basic.lean`** - Basic definitions and examples
- **`Example.lean`** - Demonstrates dual namespace patterns and basic inductive types
- **`Rosetta.lean`** - Type theory rosetta stone showing different paradigms

### Subdirectories

- **`Claude4/`** - AI-assisted implementations
  - `FSub_Claude_Tac.lean` - Tactics for System-F subtyping proofs
  - `FSub_Gemini_Def.lean` - Core definitions for System-F with subtyping
  
- **`active/`** - Currently empty, likely for active development
- **`draft/`** - Draft implementations and experiments
- **`spike/`** - Experimental code and proof-of-concepts
- **`__UNUSED/`** - Deprecated or unused code

## Dependencies

- **Lean version**: 4.22.0
- **mathlib**: v4.22.0 (comprehensive math library)
- **batteries**: v4.22.0 (extended standard library)
- **aesop**: v4.22.0 (automation tactic)

## Code Conventions

### Naming
- Use snake_case for definitions and functions
- Use PascalCase for types and structures
- Prefix with namespace (e.g., `Lp2lc.FSub`)

### Import Style
- Use quoted module names: `import «Lp2lc».module`
- Group imports logically (Lean core, external deps, local modules)

### Comments
- Use block comments for file headers: `/-...-/`
- Include attribution and conversion notes from original Rocq code
- Line comments with `--` for implementation details

### File Organization
- Each file starts with header comment explaining purpose
- Open necessary namespaces early
- Group related definitions together
- Use `namespace` blocks for organization

## Common Patterns

### Type Definitions
```lean
inductive typ : Type where
  | typ_top   : typ
  | typ_bvar  : Nat -> typ
  | typ_fvar  : Var -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_all   : typ -> typ -> typ
```

### Structure Definitions
```lean
structure Var where
  name : String
deriving Repr, BEq, Hashable, DecidableEq
```

### Elaborators and Tactics
- Use `elab` for custom syntax
- Implement `unsafe do` for meta-programming
- Log progress with `logInfo`

## Testing

The project doesn't appear to have formal tests yet. When adding tests:
- Create `*.test.lean` files
- Use `#check` for type checking
- Use `#eval` for computation verification
- Follow mathlib testing patterns

## Common Issues

- **Symbol resolution**: Use full namespace paths when importing
- **Meta-programming**: Custom elaborators require `unsafe do`
- **Finset conversion**: Converting computed values back to expressions has limitations

## Development Workflow

1. Make changes in appropriate subdirectory (`active/`, `draft/`, or `spike/`)
2. Update `Active.lean` imports if needed
3. Run `lake build` to check compilation
4. Test with `#check` and `#eval` statements

## File Patterns

- **Definitions**: End with `_Def.lean`
- **Tactics**: End with `_Tac.lean`
- **Examples**: Use `Example.lean` or descriptive names
- **Experimental**: Place in `spike/` directory
