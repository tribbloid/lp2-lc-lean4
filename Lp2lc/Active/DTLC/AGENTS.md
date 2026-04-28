
# DTLC Soundness Proof

This directory contain syntax, typing/semantic/evaluation rules and proof of soundness for DTLC (dependently-typed lambda calculus).

## Guardrails

- absolute type safety, unsafe/noncomputable/partial definition is NOT allowed.
- All definition must be with a short docString explaining their necessity.
- All function/constructor arguments must be named.
- Do NOT repeat yourself, break repeated condition in pattern matching into multiple layers of pattern matchings if applicable.
- Avoid leaky abstraction: top-level public definitions should only contain interpreter/compiler API (e.g. type-checking, evaluation). All other functions should be local inside definitions or private (only if they have multiple invocations).

## Conventions

- PHOAS (parametric higher order abstract syntx), term/type indices are irrelevant, de Bruijn serial, explicit variable name, or Env data structure are NOT allowed. (see @phoas.lean as an example).
- Semantics should only expose closed-term public APIs while keeping PHOAS-only helpers local or private.
- Big-step semantics without relying on environment or store, both type-checking and evaluation must follow functional programming style and CANNOT use contextual information. Evaluation can only happen at runtime and after successful type-checking.
- Type-checking should be rigorous and reject malformed "term: type" even if they may execute successfully (e.g. calling a term argument of "top" type which may be a function) 
- Type/term/value AST should be in a mutual block: this will be necessary for extensions.
- Extrinsic typing, term AST should not be indexed by type (impossible for mutual block due to lean compiler limitation). Type still exists in some term constructors but type-checking is semantic-only, where type become proposition/predicate of terms.
- Both compile-time type-checking and run-time evaluation/execution should use fuel-indexed guarded recursion: each level of recursive/inductive evaluation must consume 1 fuel.
- The sanity tests of Syntax and Semantic Rules are in @Tests/DTLC/Sanity.lean
