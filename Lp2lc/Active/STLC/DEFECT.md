# STLC Defects

## `Safety.proof` infrastructure

`Safety.proof` in `STLCInfer.lean` is now discharged by recursion, but it is
relative to two `ProvingEnv` obligations that are not derivable from the
current `FBound` store interface alone:

- `refSafety`: a runtime value loaded from `valueRefs` must infer to a type
  bounded by the type loaded from `typRefs` at the same index.
- `bindInfer`: if a HOAS body infers at the compile-time type binder, then the
  same body must infer at the runtime value binder when the runtime input
  satisfies the expected input type.

Concrete `ProvingEnv` instances must provide these proofs, or the environment
representation should be strengthened so they can be proved once from store
coherence.
