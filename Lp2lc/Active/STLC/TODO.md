# High Priority

- Confirmed defects from `__Infer_umbral.lean` are tracked with executable specifications in [DEFECT.md](DEFECT.md).

# Medium Priority

- for the moment, both contexts save/load a tuple: either trm2typ or trm2val.
  - this is deliberate: casting `val ~> trm` is easy. During the soundness proof, the binding of both trm and val can share a UIDEquiv.
  - reverting it is easy but doesn't offer any benefit.
  - the proof objective contains 2 parts: sameInfer (the easy part) & compilation (the bulk)
    - proving sameInfer only requires trm2typCtx.Aux0
    - proving compilation
