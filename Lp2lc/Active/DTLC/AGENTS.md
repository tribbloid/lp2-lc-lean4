
# DTLC Soundness Proof

This directory contain syntax, typing/semantic/evaluation rules and proof of soundness for DTLC (dependently-typed lambda calculus), it is like STLC but with 2 differences:

- the inclusion of a "top" type (AKA any, wildcard)
- return type of a function can depend on input value.

## Conventions

- Strong HOAS (higher order abstract syntx) + fixpoint: it's almost identical to raw Strong HOAS (see @Tests/STLC_syntax.scala for a Scala example), with one minor twist: a binded variable in a function is no longer a pending `Val`, but an unknown `{I : Index}` that can correspond to syntax or runtime values through a `Free.Fixpoint` and `UIdEquiv.Aux`. Any concrete syntax rule or AST definition can only depend on the given `{I : Index}` and the required fixpoint environment.
  - As a result, de Bruijn serial, explicit variable name, or environment/context/store definitions are NOT allowed.
- Big-step semantics, both type-checking and evaluation must follow functional programming style and only use AST information. Evaluation should only happen at runtime and after successful type-checking; compile-time checking must not call runtime `eval`.
- Type-checking should be rigorous and reject malformed "term: type" even if they may execute successfully (e.g. calling a term argument of "top" type which may be a function)
- Type/term/value AST should be in a mutual block: this will be necessary for extensions.
- Extrinsic typing, term AST should not be indexed by type (impossible for mutual block due to lean compiler limitation). Type still exists in some term constructors but type-checking is semantic-only, where type become proposition/predicate of terms.
- Both compile-time type-checking and run-time evaluation/execution should use fuel-guarded recursion: each recursive descent must consume 1 fuel.
- The test files of Syntax and Semantic Rules are in @Tests/DTLC
