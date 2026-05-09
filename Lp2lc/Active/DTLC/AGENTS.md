
# DTLC Soundness Proof

This directory contain syntax, typing/semantic/evaluation rules and proof of soundness for DTLC (dependently-typed lambda calculus), it is like STLC but with 2 differences:

- the inclusion of a "top" type (AKA any, wildcard)
- return type of a function can depend on input value.

## Guardrails

- absolute type safety, unsafe/noncomputable/partial definition is NOT allowed.
- All definition must be with a short docString explaining their necessity.
- All function/constructor arguments must be named.
- Multiple cases in pattern matching should never be in 1 line, each line should start with `|`.
- Prefer dot-notation for invoking multi-parameter functions and inductive destructors.
- Do NOT repeat yourself, break repeated condition in pattern matching into multiple layers of pattern matchings if applicable.
- Avoid leaky abstraction: top-level public APIs should only contain interpreter/compiler API (e.g. type-checking, evaluation).
- Avoid generic universe, use static Prop/Type/Sort level on-demand (Type, Type 1, Type 2)

## Conventions

- Strong HOAS (higher order abstract syntx) + F-Bound: it's almost identical to raw Strong HOAS (see @Tests/STLC_syntax.scala for a Scala example), with one minor twist: a binded variable in a function is no longer a pending `Val`, but an unknown `{I : Index}` that can corresponds to a `Val` (through a `Correspondence` type-class axiom). Any concrete syntax rule or AST definition can only depends on any given `{I : Index}` and `Correspondence` instance.
  - As a result, de Bruijn serial, explicit variable name, or environment/context/store definitions are NOT allowed.
- Big-step semantics, both type-checking and evaluation must follow functional programming style and only use AST information. Evaluation should only happen at runtime and after successful type-checking.
- Type-checking should be rigorous and reject malformed "term: type" even if they may execute successfully (e.g. calling a term argument of "top" type which may be a function) 
- Type/term/value AST should be in a mutual block: this will be necessary for extensions.
- Extrinsic typing, term AST should not be indexed by type (impossible for mutual block due to lean compiler limitation). Type still exists in some term constructors but type-checking is semantic-only, where type become proposition/predicate of terms.
- Both compile-time type-checking and run-time evaluation/execution should use fuel-guarded recursion: each level of recursive/inductive evaluation must consume 1 fuel.
- The sanity tests of Syntax and Semantic Rules are in @Tests/DTLC/Sanity.lean
