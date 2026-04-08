# Ddia conversion – questions/notes

1) Proof placement vs. project structure
- Personal rule suggests concentrating proofs under `Lp2lc/Active/Fsub.lean`.
- Project’s CodeStructure.md mandates per-Coq-file modules. I followed per-module: proofs for Ddia go in `Lp2lc/Active/Ddia/Proof.lean`.
- Please confirm this is acceptable going forward; I will adapt if you prefer centralization.

2) Environment representation
- Coq: `Definition env := LibEnv.env typ`.
- Lean: `abbrev env := List (Var × typ)`. I reuse Shared.Env helpers `domOf` and `mapSecond` and a simple `binds` via `List.lookup`.
- If you prefer a stricter `Env` API (custom record), I can refactor.

3) Binder convention and opening
- Followed Coq’s de Bruijn style and mutual opening `open_t_rec` / `open_e_rec`.
- `open_t` takes a term to open `typ_sel` occurrences (matches Coq).

4) Names and ordering
- Preserved original names where possible; avoided reserved keywords by using `def_type` / `def_term`.
- Each block in `Def.lean` includes comments noting the source Coq line ranges.

5) Progress scope
- `Proof.progress.md` enumerates all lemmas from `Ddia.v` with status = no.
- `Proof.lean` currently contains a minimal subset of stubs for structure; I will add the remaining stubs iteratively (no axioms, only `sorry`).

6) Independence
- Ddia module imports only Shared and standard libraries; it does not depend on other Active submodules, per CodeStructure.md.
