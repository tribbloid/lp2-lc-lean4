# Confirmed defects

## `Umbral.Objective` does not certify exact inference outcomes

- Status: confirmed
- Priority: high
- Fix category: Conjecture Revision
- Executable specification: [__InferUmbralSpec.lean](../../../Tests/STLC/__InferUmbralSpec.lean), section `objectiveResultMismatch`
- Reproduction: `lake build Tests.STLC.__InferUmbralSpec`

### Problem

`Objective trm` is only an alias for a recursive optional result. Its
`sameInfer` obligation is inside `ProvenCondition`, so it exists only when the
proving computation returns `Outcome.yield (some _)`. It also states that
`trm.infer` succeeds at some fuel, rather than relating both computations at
the same fuel.

Consequently, the current objective accepts a computation that returns
`Outcome.yield none` when `infer` returns `Outcome.outOfFuel`, and
`Outcome.outOfFuel` when `infer` succeeds. The current implementation also
exhibits a concrete mismatch: at fuel 3, `infer_prove` rejects the closed term
`primitiveTrueFnOnFalse` while `infer` returns `primitive`.

### Required revision

Replace the alias with a structure containing the proving computation and an
independent equality for every fuel. After erasing proof payloads, that equality
must compare the complete `Outcome (Option Typ)` returned by the proving
computation with `trm.infer`. Keep safety evidence in the successful payload;
do not use eventual inference success as the cross-computation invariant.

### Acceptance criteria

- The objective equates both computations at every fuel, including
  `Outcome.outOfFuel`, `Outcome.yield none`, and `Outcome.yield (some _)`.
- `infer_prove` constructs the strengthened objective without new `sorry`,
  axioms, `unsafe`, `noncomputable`, or `partial` declarations.
- At fuel 3, both computations return `Outcome.yield (some .primitive)` for
  `primitiveTrueFnOnFalse`.
- `lake build` passes.
