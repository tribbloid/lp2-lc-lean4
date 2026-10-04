# Inference monotonicity refutation attempt

Category: Example/Demo/Test/Benchmark, with an adversarial refutation check. No counterexample was found in
[InferRefutation.lean](InferRefutation.lean).

The adversarial examples exercise literal and reference results, absent type bindings, shifted lexical contexts,
identity and nested binders, outer captures, higher-order bindings, input type mismatches, and ghost-slot masking.
Completed successes and type failures are also compared at higher fuel using the public `AST.infer` API.
The tests infer from caller-supplied type bindings without runtime evaluation.

An application with a literal function and a child that runs out of fuel returns `outOfFuel` first, then returns
`yield none` with enough fuel. This does not refute `Monotone`: its premise requires a completed `yield` result.
Both successful and failed completed results stay identical at higher fuel in these examples.

The test file uses existing syntax constructors and demo terms, introduces no axioms or proof placeholders, and
does not duplicate the inference implementation. This finite search is evidence about the exercised cases; the
production monotonicity theorems supply the universal claims.

Validation: `lake env lean Tests/STLC/__TEMP/InferRefutation.lean` succeeds. Imported private type reindexing requires
`with_unfolding_all rfl` for direct equality assertions on this Lean version.
