# PL semantics

This module uses untyped UIds and key-value equivalence for variable binding.

- Functional binders can be applied to any UId, which is assumed to be generated only from `KVEquiv.inv`.
- As a result, there is no guarantee that they are uniform/parametric. Such properties have to be explicitly verified
      in semantics; failed verification will cause the compiler/executor to fail (return `.none`).
