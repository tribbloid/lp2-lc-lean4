# STLC TODO

- [ ] Implement `AST.Trm.compile` so every mandatory `Trm.val` hint is translated to a semantic condition and checked against the wrapped value. The current `sorry` branches do not yet reject mismatched hints, malformed applications, or invalid references.
- [x] Remove `AST.Val.compute`; a host function from `I.Data` to `Trm` is more expressive than the core simply typed lambda calculus.
- [ ] Reclassify `Trm.applyidFnOnItself` and `Trm.idFnOnFalse2` as malformed typing examples. `idFn` is annotated as `.fn .primitive .primitive`, so passing `idFn` itself as its primitive argument is not typable in STLC even though the untyped evaluator can reduce it.
- [ ] Replace the dependent singleton signatures `(v: Any) => v.type` in `Tests/Example/TrmDemo.scala` with fixed simple function types. Those signatures describe dependent typing rather than STLC and do not match the Lean `.fn .primitive .primitive` hints.
