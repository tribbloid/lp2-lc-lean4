# Confirmed defects

## Inference monotonicity audit

No counterexample or inconsistent premise was found for `AST.Monotone.termInfer` in
[Serial/__Infer.lean](Serial/__Infer.lean).

The term proposition fixes a term `Trm n` and its bindings. A build binding stores either a runtime value with
its captured environment or a hypothetical type; inference produces a type in `Typ 0`. For natural numbers
`less ≤ more`, any completed outcome
at `less` must remain identical at `more`. The quantified result is `Option (Typ 0)`, so this includes an inferred type
and `none`. An `outOfFuel` outcome is not a premise. The proposition does not assert eventual termination, typing
soundness, or monotonicity under changes to the bindings.

The same statement covers values through `value.asTrm`, which embeds the value using `.val`. It asserts no separate
value algorithm or stronger typing property. The proposition assumes no typing derivation or binder parametricity
certificate. Its premises are an ordinary natural-number inequality and a computation equality, with no inconsistent
assumption identified.

The argument slot `n + 1` overrides external bindings; all earlier slots retain their captured entries. This extension
is fixed independently of fuel. Binder bodies are opened with the same serial receipt at every fuel level.

The proofs use fuel induction and the inference equations; neither introduces a project-specific axiom.

## Mixed build bindings and runtime safety audit

No counterexample or inconsistent premise was found for the mixed-binding replacement and evaluation safety statements
in [Serial/__Infer_proof.lean](Serial/__Infer_proof.lean), including `Fundamental.main`.

Internal inference accepts `BuildBindings` directly, including hypothetical types and runtime values. Replacement
preserves every type obtainable from a source entry. A hypothetical type is retained or realized by a runtime value
that infers to it in its captured environment. Retaining a runtime entry satisfies this contract directly.

Evaluation safety uses `ExeBindings`, with every runtime entry explicitly embedded into `BuildBindings`. A hypothetical
type entry alone cannot satisfy the runtime inference premise. Resolving a closure uses its captured bindings, and the
argument slot overrides the corresponding captured entry. The statements do not claim runtime safety for arbitrary
hypothetical bindings.

The public safety theorem covers arbitrary evaluation fuel. Successful inference excludes completed evaluation
rejection; every evaluated closure admits successful inference of the original type in its captured environment.
Evaluation may exhaust its fuel, and successful inference does not assert eventual evaluation termination.

## UId scoped-origin soundness audit

No counterexample or inconsistent premise was found for the ordinary-term `fundamental` statement in
[UId/__Infer_proof.lean](UId/__Infer_proof.lean). Independent compiled examples import only
[UId/__Infer.lean](UId/__Infer.lean) and its definitions, without using the conjecture or its proof scaffold.

Public inference starts every free reference as a runtime origin. A minted type receipt is therefore rejected when
used freely, while the corresponding newest lexical slot infers its type. Giving a free reference the same receipt
as that slot does not merge their origins. Nested binders retain their outer lexical slots, including ancestor
references carried by `Under` witnesses.

Stored values restart inference under runtime origins. The audit checked direct and nested stored functions that
capture a type-only receipt, including a stored function reached beneath a lexical binder. Each rejects rather than
inheriting the hypothetical argument binding. Valid literal references still infer without an executable environment.

Mixed build minting and runtime value minting preserve canonical observations. Canonically equal callbacks have the
same inferred outcome at every fuel and the same build receipt, even when their unused callback inputs differ. The
runtime value embedding is essential: its key map cannot fix a shared minted type receipt. Neither environment
requires that key map to be the identity, and the audit made no such extra assumption.

Literal inference and evaluation require one fuel unit. A stored literal reference requires two units for inference
and one for evaluation. Identity-function inference requires two units, its literal application requires three, and
evaluation of that application requires two. The predecessor budgets exhaust fuel as expected. Type-only runtime
references and literal callees reject; successful nested lexical examples infer the expected function types.

These are kernel-checked bounded examples under the existing environment contracts, not a construction of a concrete
receipt store or a substitute for the general soundness proof. No project axiom, `sorry`, `unsafe`, `noncomputable`, or
`partial` declaration was introduced in the audit.
