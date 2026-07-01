# STLC Defects

## `Safety.proof` infrastructure

`Safety.proof` in `STLCInfer.lean` is now discharged by recursion, relative to
the keyed `ProvingEnv` store interface:

- [x] `refSafety`: a runtime value loaded from `valueRefs` must infer to a type
  bounded by the type loaded from `typRefs` at the same index.
- [x] `bindInfer`: if a Val.fn body infers at the compile-time type binder, then the
  same body must infer at the runtime value binder when the runtime input
  satisfies the expected input type.

Concrete `ProvingEnv` instances still provide `refSafety`; `bindInfer` is now
derived from shared base-index coherence plus `PHOASCoherence.inferStable`.
