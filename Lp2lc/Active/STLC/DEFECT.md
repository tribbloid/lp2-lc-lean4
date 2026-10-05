# Confirmed defects

## Inference monotonicity audit

No counterexample or inconsistent premise was found for `AST.termInferMonotone` or `AST.valueInferMonotone` in
[Serial/__Infer.lean](Serial/__Infer.lean).

The term proposition fixes a term `Trm n` and a binding function. Each binding stores a runtime value with its
captured environment; inference derives its type in `Typ 0`. For natural numbers `less ≤ more`, any completed outcome
at `less` must remain identical at `more`. The quantified result is `Option (Typ 0)`, so this includes an inferred type
and `none`. An `outOfFuel` outcome is not a premise. The proposition does not assert eventual termination, typing
soundness, or monotonicity under changes to the binding function.

The value proposition applies the same statement to `value.asTrm`, which embeds the value using `.val`. It asserts
no separate value algorithm or stronger typing property. Neither proposition assumes a typing derivation or a
binder parametricity certificate. Their premises are an ordinary natural-number inequality and a computation
equality, with no inconsistent assumption identified.

The ghost slot `n + 1` is unavailable and the argument slot `n + 2` overrides external bindings. These extensions
are fixed independently of fuel. Binder bodies are opened with the same serial receipt at every fuel level.

The proofs use fuel induction and the inference equations; neither introduces a project-specific axiom.
