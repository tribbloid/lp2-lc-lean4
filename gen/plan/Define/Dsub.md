# Dsub - Define conversion plan

- Coq file: Lp2lc_coq/Active/Dsub.v (approx 1774 lines)
- Lean module: Lp2lc/Active/Dsub/

Overview and scope
- Convert all definitions, types, and axioms 1:1; preserve order and names with [Coq L###] comments.

Current Lean status (snapshot)
- Def.lean: types/terms, opening, lc (def_type/def_term), env, wft/wfe, sub/has, typing, red, fv, subst present.
- Proof.lean: theorem scaffolding with `sorry` bodies.
- Auxiliary.lean: minimal ok : env → Prop axiom.

TODOs and deltas
- Cross-check against gen/plan/Define/Dsub.coq.index to ensure 1:1 coverage.
- Fill Def.progress.md and Proof.progress.md rows for every Coq declaration.
- Ensure all definitions include [Coq L###] comments (strictly incremental).

Steps
- Definition audit → Proof scaffolding audit → Update progress docs → Build → Commit.

Notes
- Keep Prop; no cross-module imports; Aesop attrs may mirror Coq Hints.
