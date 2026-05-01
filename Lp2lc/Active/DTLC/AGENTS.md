
# DTLC Soundness Proof

This directory contain syntax, typing/semantic/evaluation rules and proof of soundness for DTLC (dependently-typed lambda calculus).

## Guardrails

- absolute type safety, unsafe/noncomputable/partial definition is NOT allowed.
- All definition must be with a short docString explaining their necessity.
- All function/constructor arguments must be named.
- Multiple cases in pattern matching should never be in 1 line, each line should start with `|`.
- Prefer dot-notation for invoking multi-parameter functions and inductive destructors.
- Do NOT repeat yourself, break repeated condition in pattern matching into multiple layers of pattern matchings if applicable.
- Avoid leaky abstraction: top-level public APIs should only contain interpreter/compiler API (e.g. type-checking, evaluation). evaluator/checker helpers of PHOAS should be kept local to to each API, only helpers reused by multiple public APIs may be private.
- Avoid generic universe, use static Prop/Type/Sort level on-demand (Type, Type 1, Type 2)

## Conventions

- PHOAS (parametric higher order abstract syntx), term/type indices are irrelevant, de Bruijn serial, explicit variable name, or Env data structure are NOT allowed. (see @phoas.lean as an example).
- Big-step semantics without relying on environment or store, both type-checking and evaluation must follow functional programming style and CANNOT use contextual information. Evaluation can only happen at runtime and after successful type-checking.
- Type-checking should be rigorous and reject malformed "term: type" even if they may execute successfully (e.g. calling a term argument of "top" type which may be a function) 
- Type/term/value AST should be in a mutual block: this will be necessary for extensions.
- Extrinsic typing, term AST should not be indexed by type (impossible for mutual block due to lean compiler limitation). Type still exists in some term constructors but type-checking is semantic-only, where type become proposition/predicate of terms.
- Both compile-time type-checking and run-time evaluation/execution should use fuel-guarded recursion: each level of recursive/inductive evaluation must consume 1 fuel.
- The sanity tests of Syntax and Semantic Rules are in @Tests/DTLC/Sanity.lean
