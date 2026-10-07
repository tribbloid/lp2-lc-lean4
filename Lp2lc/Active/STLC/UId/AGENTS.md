# PL semantics

This module uses untyped UId and Key-Value equivalence for variable binding

- Functional binders can be applied to any UId, which are assumed to be only generated from KVEquiv.inv and nowhere else.
- ... as a result, there is no guarantee that they are uniform/parametric. Such properties have to be explicitly verified in semantics, failed verification will cause compiler/executor to fail (return .none).
