# Confirmed defects

## Raw `trm2typCtx` UIDs can bypass proposed Umbral safety evidence

- Status: confirmed design defect; latent in the current implementation
- Priority: high
- Fix category: Conjecture Revision
- Executable specification: [__InferUmbralSpec.lean](../../../Tests/STLC/__InferUmbralSpec.lean), section `aux0SafetyContextCollapse`
- Reproduction: `lake build Tests.STLC.__InferUmbralSpec`

### Scope

The current `ProvingEnv` contains only `base`, and the current `infer_prove`
returns `Outcome.yield none` for references. There is therefore no live
`Aux0`-based proof context to exploit. The defect is in the proposed addition
of such a context: implementing that plan would make the soundness environment
inconsistent.

### Problem

`UIDEquiv.Aux0.invEv` accepts any raw UID. For any value `v`, calling
`invEv (outer.getUID v)` produces metadata for `outer.inv (outer.getUID v)`,
which `UIDEquiv.leftInv` reduces to metadata for `v`. No call to `Aux0.getEv`
and no proof that the value was saved are required.

Consequently, specializing the metadata to
`Safety trm2typ.trm trm2typ.typ` proves every `Trm2Typ` safe. The executable
specification constructs a raw UID for a primitive value applied as a function,
recovers a safety proof through the proposed `Aux0`, and contradicts the
term's `Outcome.yield none` evaluation at fuel 2.

This is a loss of evidence provenance, not a collision between distinct UID
values. The raw UID crosses from the base `trm2typCtx` into its auxiliary store
without a store-specific membership witness.

### Required revision

- Use `UIDEquiv.Aux`, never `Aux0`, for the Umbral safety store.
- Require the exact auxiliary-store membership witness, such as
  `proofCtx.AuxUID`, when recovering safety evidence.
- Make references in the proving path carry that witness, or an equivalent
  dependent capability tied to the exact store. A subtype with an unrelated
  predicate is insufficient.
- Rewrite the lambda and reference paths of `infer_prove` after the evidence
  boundary is established.

### Acceptance criteria

- The Umbral proof context contains no `Aux0`.
- A raw `trm2typCtx.getUID trm2typ` cannot recover safety evidence or construct
  a reference accepted by the soundness path.
- `Aux.getEv ⟨trm2typ, safety⟩` produces the witness required by
  `Aux.invEv`, and this authorized round trip compiles.
- Add a guarded negative elaboration check for the rejected raw-UID path and a
  positive authorized-reference check.
- `lake build` passes without new `sorry`, axioms, `unsafe`, `noncomputable`, or
  `partial` declarations.
