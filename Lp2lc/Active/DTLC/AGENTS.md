
# DTLC Soundness Proof

This directory contain syntax, typing/semantic/evaluation rules and proof of soundness for DTLC (dependently-typed lambda calculus).

## Conventions

- PHOAS (parametric higher order abstract syntx), term/type indices are irrelevant, no de Bruijn serial, explicit variable name, or Env data structure allowed. (see @phoas.lean as an example)
- Big-step semantics without relying on environment or store, typing and evaluation rules are 100% functional and can only use data included in type/term AST.
- Type/term/value AST are in a mutual block: this will be necessary later.
- Extrinsic typing, term AST should not be indexed by type (impossible for mutual block due to lean compiler limitation). Type still exists in some term constructors but type-checking is semantic-only, where type become proposition/predicate of terms.
- Both compile-time type-checking and run-time evaluation/execution should use fuel-indexed Kripke frames with "Later" modality: each level of recursive/inductive evaluation must consume 1 fuel.
- The sanity tests of Syntax and Semantic Rules are in @Tests/DTLC/Sanity.lean