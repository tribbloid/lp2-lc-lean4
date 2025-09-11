# Define.md summary and checklist (Active)

This summarizes prompt/Define.md for the Active conversion (Coq → Lean 4).

Workflow
1) Source scan
- List all Coq files under Lp2lc_coq/Active and rank by size (ascending).
- Read lakefile.lean (done) to verify deps (aesop, batteries, mathlib).

2) File structure setup
- For each Coq file X.v, map to Lean module directory Lp2lc/Active/X/ with:
  - Def.lean, Proof.lean, Auxiliary.lean,
  - Def.progress.md, Proof.progress.md, specs.md.
- Preserve existing files; do not delete or remove contents.

3) Planning
- For each pair (X.v, Lp2lc/Active/X), verify structure as above.
- Update Def.progress.md to list Coq defs/axioms/types and their Lean counterparts.
- Update Proof.progress.md to list Coq theorems/lemmas and the Lean stubs, with Proven? = no while scaffolding.

4) Conversion (iterative, build after each change)
- 4.1 Definitions: Extract Coq defs/axioms/types, convert to Lean syntax, write into Def.lean with original Coq line number comments.
- 4.2 Proof scaffolding: Extract theorems/lemmas; create theorem statements in Proof.lean with sorry bodies, keeping the original order. Do not attempt to prove.
- 4.3 Verification: Compare Def.progress.md and Proof.progress.md against sources; continue from where they differ.

5) Aggregation
- Check that every Coq file is mirrored by a Lean module.

Rules
- Preserve original names and order; only prefix with def_ if Lean syntax demands.
- Prefix each declaration with a comment indicating original Coq line number (strictly incremental).
- Use “sorry” with a TODO for any incomplete proof.
- Coq Set/Prop → Lean Prop, Type → Prop only if possible; use Type u for ASTs.
- LibLN’s Var → Lean structure Var with String field (provided in Lp2lc/Shared.lean).
- Hint Constructors/Resolve → use Aesop attributes in Auxiliary when helpful.
- LibEnv ok: keep a minimal abstract ok : env → Prop in Auxiliary to typecheck statements.

Project-specific constraints
- Modules are independent; do not import each other’s Lean files.
- Code shared between modules lives in /Lp2lc/Shared.lean.
- Only write under Lp2lc/Active and gen/plan/… docs for planning.

Execution policy (user preferences)
- Proceed without additional prompts.
- Later, when proving, prioritize (a) theorems first, (b) smaller line numbers first.
- Ignore any draft directories.
