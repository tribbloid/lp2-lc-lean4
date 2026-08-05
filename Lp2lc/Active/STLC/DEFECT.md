# Confirmed defects

No active defects.

## Standing requirements: Umbral `proofCtx` evidence boundary

The following requirements constrain the future `proofCtx` store in
`Umbral.ProvingEnv` (see the TODO in `__Infer_umbral.lean`). They exist
because the previous design was confirmed unsound and removed in commit
4d50cc0.

### Background

The removed `UIDEquiv.Aux0` recovered metadata from any raw UID:
`invEv : (uid : UID) → M (outer.inv uid)`. Because `UIDEquiv` is a
bijection (`leftInv`/`rightInv`), such total recovery is equivalent to
`∀ v, M v`. Specialized to `M := λ trm2typ => Safety trm2typ.trm trm2typ.typ`,
it proves every `Trm2Typ` safe, which is refutable: a primitive value
applied as a function evaluates to `.yield none` at fuel 2. The executable
demonstration was removed together with the class; see the git history of
`Tests/STLC/__InferUmbralSpec.lean`.

This is an evidence-provenance requirement, not a UID-collision concern:
raw UIDs from the base `trm2typCtx` must not cross into its auxiliary
store without a store-specific membership witness.

### Requirements

- The safety store must be a `UIDEquiv.Aux` over the base `trm2typCtx`;
  total evidence recovery from raw UIDs is unsound and must not be
  reintroduced in any form.
- Safety evidence is recovered only through `Aux.invEv`, which requires
  the store's membership witness `Aux.AuxUID` (`PSigma Ev`).
- `Ev` must be defined from the save path so that it is only inhabited
  for UIDs saved through `Aux.getEv`; a constant-true or otherwise
  unrelated predicate voids the boundary.
- References in the proving path must carry that witness, or an
  equivalent dependent capability tied to the exact store.

### Acceptance criteria for the `proofCtx` task

- `Aux.getEv ⟨trm2typ, safety⟩` produces the witness required by
  `Aux.invEv`; the authorized round trip compiles (cf.
  `Aux.leftInvValue`).
- A raw `trm2typCtx.getUID trm2typ` cannot recover safety evidence or
  construct a reference accepted by the soundness path; add a guarded
  negative elaboration check for the rejected raw-UID path and a
  positive authorized-reference check in
  `Tests/STLC/__InferUmbralSpec.lean`.
- `lake build` passes without new `sorry`, axioms, `unsafe`,
  `noncomputable`, or `partial` declarations.
