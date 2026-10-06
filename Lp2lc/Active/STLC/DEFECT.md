# Confirmed defects

## Inference monotonicity audit

No counterexample or inconsistent premise was found for `AST.Monotone.termInferMonotone` or
`AST.Monotone.valueInferMonotone` in
[Serial/__Infer.lean](Serial/__Infer.lean).

The term proposition fixes a term `Trm n` and a binding function. A build binding stores either a runtime value with
its captured environment or a hypothetical type; inference produces a type in `Typ 0`. For natural numbers
`less ≤ more`, any completed outcome
at `less` must remain identical at `more`. The quantified result is `Option (Typ 0)`, so this includes an inferred type
and `none`. An `outOfFuel` outcome is not a premise. The proposition does not assert eventual termination, typing
soundness, or monotonicity under changes to the binding function.

The value proposition applies the same statement to `value.asTrm`, which embeds the value using `.val`. It asserts
no separate value algorithm or stronger typing property. Neither proposition assumes a typing derivation or a
binder parametricity certificate. Their premises are an ordinary natural-number inequality and a computation
equality, with no inconsistent assumption identified.

The argument slot `n + 1` overrides external bindings; all earlier slots retain their captured entries. This extension
is fixed independently of fuel. Binder bodies are opened with the same serial receipt at every fuel level.

The proofs use fuel induction and the inference equations; neither introduces a project-specific axiom.

## Mixed build bindings and runtime safety audit

No counterexample or inconsistent premise was found for the mixed-binding replacement and evaluation safety statements
in [Serial/__Infer.lean](Serial/__Infer.lean), or for `Safety`, `fundamental`, and `paranoidFundamental` in
[Serial/__Infer_proof.lean](Serial/__Infer_proof.lean).

Inference accepts `BuildBindings` directly, including hypothetical types and runtime values. Replacing a type entry
requires a runtime value that infers to the identical type in its captured environment. Existing runtime entries must
remain identical. These premises prevent replacement from changing a successful inferred result.

Evaluation safety uses `ExeBindings`, with every runtime entry explicitly embedded into `BuildBindings`. A hypothetical
type entry alone cannot satisfy the runtime inference premise. Resolving a closure uses its captured bindings, and the
argument slot overrides the corresponding captured entry. The statements do not claim runtime safety for arbitrary
hypothetical bindings.
