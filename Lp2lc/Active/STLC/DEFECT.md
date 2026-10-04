# Confirmed defects

## Inference monotonicity audit

No counterexample or inconsistent premise was found for `AST.termInferMonotone` or `AST.valueInferMonotone` in
[Serial/__Infer.lean](Serial/__Infer.lean).

The term proposition fixes a term `Trm n` and a binding function. Each binding may store a type from an arbitrary
context; inference converts it to `Typ 0`. For natural numbers `less ≤ more`, any completed outcome at `less` must
remain identical at `more`. The quantified result is `Option (Typ 0)`, so this includes both an inferred type and
`none`. An `outOfFuel` outcome is not a premise. The proposition does not assert eventual termination, typing
soundness, or monotonicity under changes to the binding function.

The value proposition applies the same statement to `value.asTrm`, which embeds the value using `.val`. It asserts
no separate value algorithm or stronger typing property. Neither proposition assumes a typing derivation or a
binder parametricity certificate. Their premises are an ordinary natural-number inequality and a computation
equality, with no inconsistent assumption identified.

The adversarial audit in [InferRefutation.lean](../../../Tests/STLC/__TEMP/InferRefutation.lean) checks bindings from
different contexts, nested function types, free capture, higher-order arguments, missing references, the ghost
slot, ill-typed applications, and fuel exhaustion in an argument even when the function cannot be applied.
The ghost slot `n + 1` is unavailable and the argument slot `n + 2` overrides external bindings. These extensions
are fixed independently of fuel. Binder bodies are opened with the same serial receipt at every fuel level.
The audit also checks literal success, missing-reference rejection, and ghost-reference rejection for arbitrary
additional fuel by reduction, without invoking either monotonicity theorem.

Kernel axiom reports for both existing proofs contain only `propext` and `Quot.sound`; neither depends on
`sorryAx` or a project-specific axiom. Guarded reports in the audit detect changes to these dependencies.
