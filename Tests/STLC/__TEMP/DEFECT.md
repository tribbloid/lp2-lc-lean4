# Inference monotonicity refutation attempt

Category: Example/Demo/Test/Benchmark, with an adversarial refutation check. No counterexample was found in
[InferRefutation.lean](InferRefutation.lean).

The adversarial examples exercise literal and reference results, absent type bindings, shifted lexical contexts,
identity and nested binders, outer captures, higher-order bindings, input type mismatches, and ghost-slot masking.
Stored types retain dependent context pairs; examples also resolve types originating in unrelated lexical contexts.
Completed successes and type failures are also compared at higher fuel using the public `AST.infer` API.
The tests infer from caller-supplied type bindings without runtime evaluation. Direct type and value checks, literal
terms, references, nested functions, and applications exercise the exact boundary where resolution runs out of fuel.
Every syntax resolution consumes one unit, including stored type syntax reached through a reference.

An application with a literal function and a child that runs out of fuel returns `outOfFuel` first, then returns
`yield none` with enough fuel. This does not refute `Monotone`: its premise requires a completed `yield` result.
A missing body reference also preserves `outOfFuel` while its larger input annotation remains unresolved, then
returns `yield none` when the annotation finishes. Both successful and failed completed results stay identical at
higher fuel in these examples.

The test file uses existing syntax constructors and demo terms, introduces no axioms or proof placeholders, and
does not duplicate the inference implementation. This finite search is evidence about the exercised cases; the
production monotonicity theorems supply the universal claims.

Validation: `lake build Tests.STLC.__TEMP.InferRefutation` succeeds. All equality assertions use `rfl`;
there is no private type reindexing helper.
