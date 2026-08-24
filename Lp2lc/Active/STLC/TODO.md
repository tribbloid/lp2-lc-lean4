# High Priority

## Separate free and bound receipts with pure PHOAS

The current lambda body receives one carrier containing both captured runtime references and compiler-introduced binder receipts. This permits an exotic term to inspect whether its body was instantiated by evaluation or inference.

Replace that carrier with distinct free and bound receipt carriers while retaining PHOAS. This is a representation refactor followed by separate semantic reviews; it is not permission to add a context representation, receipt bridge, or proof assumption.

### Try to construct a counterexample for compiler adequacy/soundness

After all implementation and test commits, assign a different subagent to try to construct a new executable term for which `Trm.infer` succeeds but evaluation violates the inferred type. At minimum it must attempt:

- comparing a bound receipt with a captured free receipt;
- comparing two nested bound receipts with the same input type but different runtime values;
- obtaining a bound inhabitant through `Inhabited`/`default` or observing it through `DecidableEq`, `BEq`, `Hashable`, `Ord`, or `Repr`;
- importing a `B → F`, `B → Bool`, or receipt conversion through a public class, coercion, mapper, stored value, or environment projection;
- specializing a term to a concrete runtime `B` before passing it to inference;
- mapping/recarriering an AST across two bound carriers; and
- reproducing the current `TestEnv.decidableEq` attack or otherwise forging a missing free or bound value/type receipt.

This counterexample subagent must fail to write such a term using the production API and must report why each attempt is unrepresentable. A failure caused only by an unrelated elaboration error is not evidence. It must also exercise ordinary nested binders and free capture as positive controls. If any attack succeeds, the refactor and Umbral discharge are not complete: preserve or add the term in the paired Lean/Scala demo and evaluation/inference regression-test format, then return to the representation design.

### Validation

- For each commit, run the relevant targeted `lake build` modules, then the complete `lake build` and `git diff --check` before moving on.
- Compile the Scala demos after their migration.
- Verify the runtime/compiler capability boundary by inspection: evaluation alone can mint `uid2val` receipts, inference alone can mint `uid2typ` receipts, and neither side contains a cross-phase conversion.
- Use `#print axioms` on `AST.eval`, `AST.infer`, and the discharged Umbral theorem as part of the final assumption inventory.
- Require both final subagent reports: the assumption/capability audit must find no new abstract power, and the counterexample subagent audit must fail to produce a counterexample.
