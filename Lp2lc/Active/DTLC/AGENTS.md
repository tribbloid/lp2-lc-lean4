
# DTLC Soundness Proof

This directory contain syntax, typing/semantic/evaluation rules and proof of soundness for DTLC (dependently-typed lambda calculus).

## Conventions

- PHOAS (parametric higher order abstract syntx), term/type indices are irrelevant, no de Bruijn serial, explicit variable name, or Env data structure allowed. (see @phoas.lean as example)
- Type/term/value AST are in a mutual block: this will be necessary later.
- Extrinsic typing, term AST should not be indexed by type, this is impossible for mutual block due to lean compiler limitation. Type still exists in some term constructors but they are evaluated into semantics types, which are predicates for terms (term -> proposition).
- Definitional semantics only, terms are mapped into interpretable lean object (either values or lean functions that produces value directly or indirectly)
- Step-indexed evaluation/interpretation using "Later" modality: each level of recursive/inductive evaluation must consume 1 fuel, in both compile-time and run-time.