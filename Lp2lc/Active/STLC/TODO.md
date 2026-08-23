# High Priority

## Separate free references from representation-independent bound variables

The current lambda body receives one carrier containing both captured runtime
references and compiler-introduced binder receipts. This permits exotic terms
whose syntax depends on whether the body is instantiated by evaluation or
inference.

Splitting the carrier into free and bound variables is necessary, but the bound
variable itself must not be a semantic `uid2val` or `uid2typ` receipt. Otherwise
nested binders remain unsound: two primitive parameters have the same type
receipt during inference but may have different value receipts during
evaluation, so a body can branch on their equality. The current implementation
has a compiler-checked example that infers `.primitive` at fuel 5 and evaluates
to failure at fuel 4.

### Required representation

- Replace `Parameters.C` with separate free and bound carrier parameters `F`
  and `B`, retaining `D`.
- Let `.ref` distinguish both sources, for example with a carrier `F ⊕ B`.
- Make `.lam` extend only the bound scope. Prefer a structural scope extension
  `B ⊕ Unit`: existing bound variables use `.inl`, and the newly introduced
  variable is `.inr ()`. Do not provide a coercion from `F` into `B`.
- Keep bound tokens identical across evaluation and inference. Evaluation uses
  a resolver from `B` to `uid2val` receipts; inference uses a resolver from the
  same `B` to `uid2typ` receipts. Extending a lambda extends only the applicable
  resolver.
- Free references remain backed by `uid2val` in both phases. Compiler code must
  retain only the read-only value view and must not gain `ExeEnv` or runtime
  receipt-minting capability.
- Revise `AST.map`/recarriering so free references are mapped normally and bound
  renaming is lifted structurally through `B ⊕ Unit`.

### Migration and acceptance

- Migrate the AST aliases, environments, evaluation, inference, monotonicity
  proofs, demos, and Umbral consumers to the separated representation.
- Check both exotic-term shapes before claiming safety: comparison of a bound
  variable with a captured free reference, and comparison of two nested bound
  variables with the same input type but different runtime values.
- Remove `binderIdentityCounterexample`, its Scala counterpart, its evaluation
  and inference tests, and the fixture-only `TestEnv.decidableEq` field only
  after the revised syntax makes the mismatch impossible. If either shape still
  produces differing inference/evaluation behavior, keep or add it in the same
  paired demo and regression-test format and do not discharge Umbral inference.
- Keep the syntax/conjecture revision and the later proof discharge in separate
  independently reviewed commits. Introduce no new `sorry`, axioms, `unsafe`,
  or `noncomputable` declarations.
- Validate the relevant targeted modules, the complete `lake build`, Scala demo
  compilation, `git diff --check`, and compiler/runtime capability boundaries.
