# High Priority

## Separate free and bound receipts with pure PHOAS

The current lambda body receives one carrier containing both captured runtime
references and compiler-introduced binder receipts. This permits an exotic
term to inspect whether its body was instantiated by evaluation or inference.

Replace that carrier with distinct free and bound receipt carriers while
retaining PHOAS. This is a representation refactor followed by separate
semantic reviews; it is not permission to add a context representation,
receipt bridge, or proof assumption.

### Required representation

- Replace `Parameters.C` with `F : UIdU` and `B : UIdU`, retaining `D`.
  `F` and `B` are always UId/receipt carriers in concrete AST and environment
  parameters; do not replace either one with a scope token, `Unit`, `Fin`, a
  context entry, or any other binder representation.
- Let `AST.ref` refer to either receipt source, using `F ⊕ B` (or the
  definitionally equivalent separated form). A free reference is always an
  `F` receipt and a lambda-bound reference is always a `B` receipt.
- Let `AST.lam` introduce only a `B`. Its body has the essential shape
  `B → AST { F := F, B := B, D := D } .trm`; remove the carrier-polymorphic
  `{C}` binder, `Greater`, and every route from `F` into the function argument.
  Captured outer binders remain values of the same `B`, as required by PHOAS.
- Make all executable/source terms and values stored by `ExeRefs.uid2val`
  polymorphic in `B`. Evaluation and inference must instantiate that
  polymorphism directly; a stored runtime-bound AST must never be recarriered
  into the compiler-bound AST.
- Evaluation instantiates `B` as `refs.uid2val.UId`; inference independently
  instantiates `B` as `build.uid2typ.UId`. This instantiation is the whole phase
  mapping: there must be no function that maps an abstract `B` to either receipt
  family.
- During evaluation, both free and bound references are `uid2val` receipts.
  During inference, free references remain `uid2val` receipts and bound
  references are `uid2typ` receipts.
- A lambda application may mint its bound receipt only with the existing
  `ExeEnv.uid2valCtx.inv`. Lambda inference may mint its bound receipt only with
  the existing `BuildEnv.uid2typCtx.inv`. Free references are looked up through
  the existing read-only `ExeRefs.uid2val` view in both phases.
- Retype `ExeRefs`, `ExeEnv`, `BuildEnv`, the AST aliases, and `AST.map` only as
  required by those two carriers. `AST.map` may change the free carrier and data
  while keeping `B` fixed; it must not map between bound carriers or manufacture
  a runtime/build relation.
- Do not introduce `ConsList`, a context object, a resolver/substitution table,
  de Bruijn indices, `B ⊕ Unit`, a scoped-carrier type, or any other new
  binding concept. The function body itself is the PHOAS binding context.

### Hard assumption and capability guardrail

- Introduce no new `axiom`, `opaque`, `sorry`, `admit`, `unsafe`,
  `noncomputable`, or use of `Classical`.
- Introduce no new abstract class/structure field or typeclass assumption. The
  sole permitted class-shape change is replacing the data-free type field
  `Parameters.C` with the data-free type fields `Parameters.F` and
  `Parameters.B`; existing `ExeRefs`, `ExeEnv`, `BuildEnv`, and `ProvingEnv`
  fields may be retyped but not augmented.
- `ExeRefs` must retain only `D` and `uid2val`; `ExeEnv` only `uid2valCtx`;
  `BuildEnv` only `uid2typ` and `uid2typCtx`. `ProvingEnv` may retain its current
  derived field but may not gain another one.
- In particular, do not add a receipt resolver, receipt conversion, receipt
  equality, `DecidableEq F`, `DecidableEq B`, `Coe F B`, `Greater`, context
  lookup, parametricity witness, safety witness, or receipt-minting operation.
  Do not expose `ExeEnv` or `uid2valCtx.inv` to compiler code.
- Concrete proved helper definitions and lemmas are allowed when necessary,
  but every proposition must be proved from the existing `ExeEnv` and
  `BuildEnv` APIs. No helper may conceal a new assumption or abstract operation.
- Before the refactor and again at the final candidate, inventory declarations
  and assumptions (`axiom`, class/structure fields, `#print axioms`, `sorry`,
  `admit`, `unsafe`, `noncomputable`, and `Classical`). A reviewing subagent
  must compare both inventories and inspect the diff. Its review must explicitly
  confirm that no new axiom, abstract field, or capability was introduced; any
  exception blocks the task.

### Small, independently reviewable commits

Every commit must build before the next one begins. Signature-forced downstream
edits may accompany the first commit only when they are mechanical and required
to keep the tree buildable; semantic changes and tests belong to the named
later commit.

1. **Parameters and AST representation.** Replace `C` by `F` and `B`; revise
   `AST.ref`, `AST.lam`, the PHOAS-polymorphic term/value aliases, `AST.map`, and
   the receipt-indexed value-family signatures. Make only mechanical downstream
   type adaptations, and do not discharge or revise the Umbral proposition.
2. **Evaluation review.** Review and revise only the evaluation path so both
   carriers instantiate to `uid2val.UId`, `.ref` handles free and bound
   receipts through `uid2val`, and `.lam` uses only `uid2valCtx.inv`. Add or
   adapt evaluation tests in the same commit.
3. **Inference review.** Review and revise only `BuildEnv` and the inference
   path so `F` is `uid2val.UId`, `B` is `uid2typ.UId`, free lookup remains
   read-only, and `.lam` uses only `uid2typCtx.inv`. Add or adapt `Trm.infer`
   tests in the same commit; compiler code must not acquire `ExeEnv`.
4. **Proof and consumer migration.** In separate small commits, migrate the
   monotonicity/safety statements and proofs, Umbral consumers, then remaining
   demos and downstream modules. Do not combine proposition revision with
   proof discharge.
5. **Retire the obsolete counterexample.** Once the new AST makes the existing
   `binderIdentityCounterexample` unrepresentable, remove its Lean and Scala
   demos, its evaluation and inference tests, and the fixture-only
   `TestEnv.decidableEq` support in one test-only commit. It must no longer be
   described or retained as a counterexample against `Trm.infer` safety.
6. **Umbral feasibility gate.** Before proof work, verify that runtime-`B` and
   build-`B` instantiations can be related constructively from the AST and the
   existing environments. Failure to find a lawful closed counterexample is
   necessary but is not a replacement for this proof: Lean does not supply a
   relational-parametricity theorem for an arbitrary polymorphic term. If the
   proof would require such an axiom or abstract operation, stop and report the
   theorem as infeasible under this guardrail.
7. **Umbral discharge.** Only after the feasibility gate, discharge the existing
   TODO in its own proving commit, without changing the proposition and without
   introducing an assumption. Obtain the task-required proving/discharge
   subagent review before accepting this commit.

### Adversarial safety gate

After all implementation and test commits, assign a different subagent to try
to construct a new executable term for which `Trm.infer` succeeds but evaluation
violates the inferred type. At minimum it must attempt:

- comparing a bound receipt with a captured free receipt;
- comparing two nested bound receipts with the same input type but different
  runtime values;
- obtaining a bound inhabitant through `Inhabited`/`default` or observing it
  through `DecidableEq`, `BEq`, `Hashable`, `Ord`, or `Repr`;
- importing a `B → F`, `B → Bool`, or receipt conversion through a public
  class, coercion, mapper, stored value, or environment projection;
- specializing a term to a concrete runtime `B` before passing it to inference;
- mapping/recarriering an AST across two bound carriers; and
- reproducing the current `TestEnv.decidableEq` attack or otherwise forging a
  missing free or bound value/type receipt.

The adversarial subagent must fail to write such a term using the production
API and must report why each attempt is unrepresentable. A failure caused only
by an unrelated elaboration error is not evidence. It must also exercise
ordinary nested binders and free capture as positive controls. If any attack
succeeds, the refactor and Umbral discharge are not complete: preserve or add
the term in the paired Lean/Scala demo and evaluation/inference regression-test
format, then return to the representation design.

### Validation

- For each commit, run the relevant targeted `lake build` modules, then the
  complete `lake build` and `git diff --check` before moving on.
- Compile the Scala demos after their migration.
- Verify the runtime/compiler capability boundary by inspection: evaluation
  alone can mint `uid2val` receipts, inference alone can mint `uid2typ`
  receipts, and neither side contains a cross-phase conversion.
- Use `#print axioms` on `AST.eval`, `AST.infer`, and the discharged Umbral
  theorem as part of the final assumption inventory.
- Require both final subagent reports: the assumption/capability audit must
  find no new abstract power, and the adversarial safety audit must fail to
  produce a counterexample.
