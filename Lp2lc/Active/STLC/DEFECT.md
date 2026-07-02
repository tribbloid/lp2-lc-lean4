# STLC Defects

## `Safety.proof` infrastructure

`Safety.proof` in `STLCInfer.lean` is now discharged by recursion. It still
depends on `ProvingEnv.refSafety` and PHOAS inference coherence:

- [x] `refSafety`: a runtime value loaded from `valueRefs` must infer to a type
  bounded by the type loaded from `typRefs` at the same index.
- [x] `PHOASCoherence.inferStable`: if a Val.fn body infers at the compile-time type binder, then the
  same body must infer at the runtime value binder when the runtime input
  satisfies the expected input type.

Concrete `ProvingEnv` instances must provide `refSafety` and the PHOAS
coherence instance used by `Safety.proof`.
