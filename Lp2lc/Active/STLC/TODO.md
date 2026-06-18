# STLC TODO

- [ ] Implement `AST.Trm.compile` so every mandatory `Trm.val` hint is translated to a semantic condition and checked against the wrapped value. The current `sorry` branches do not yet reject mismatched hints, malformed applications, or invalid references.
- [x] Remove `AST.Val.compute`; a host function from `I.Data` to `Trm` is more expressive than the core simply typed lambda calculus.
- [x] Reclassify `Trm.applyidFnOnItself` and `Trm.idFnOnFalse2` as malformed typing examples. `primitiveIdFn` is annotated as `.fn .primitive .primitive`, so passing `primitiveIdFn` itself as its primitive argument is not typable in STLC even though the untyped evaluator can reduce it.
- [x] Use the fixed-typed `primitiveIdFn` examples from `Tests/Example/TrmDemo.scala` in `Tests/STLC/TrmDemo.lean`; the dependent `idFn` examples are not supported by STLC.
