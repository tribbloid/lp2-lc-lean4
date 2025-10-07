# Glossary for DOT with top/bot — `Dot_top_bot`

This glossary explains the lemmas/theorems in `Lp2lc_coq/Active/Dot_top_bot.v`, grouped by topic, and notes the Lean counterparts under `Lp2lc/Active/Dot_top_bot/Proof.lean` where present.

Legend:
- Coq name: identifier in `Dot_top_bot.v`.
- Lean name: corresponding `theorem` in Lean (if present).
- Meaning: concise purpose/role in the development.

## Infrastructure
- **[fresh_push_eq_inv]** (Lean: `fresh_push_eq_inv`) — Freshness contradiction: a variable cannot be fresh in an environment where it is just pushed.

## Weakening
- **[weaken_rules]** (Lean: `weaken_rules`) — Mutual weakening for `ty_trm`, `ty_def`, `ty_defs`, and `subtyp`: if a judgment holds under `G1 & G3`, it holds under `G1 & G2 & G3` when that env is ok.
- **[weaken_ty_trm]** (Lean: `weaken_ty_trm`) — Term typing preserved by environment weakening.
- **[weaken_subtyp]** (Lean: `weaken_subtyp`) — Subtyping preserved by environment weakening.

## Well-formed store
- **[wf_sto_to_ok_s]** (Lean: `wf_sto_to_ok_s`) — Well-formed store implies the store environment is `ok` (no duplicates).
- **[wf_sto_to_ok_G]** (Lean: `wf_sto_to_ok_G`) — Well-formed store implies the typing context is `ok`.

## Store-context relations
- **[ctx_binds_to_sto_binds_raw]** (Lean: `ctx_binds_to_sto_binds_raw`) — If `wf_sto G s` and `x : T ∈ G`, then there exist `G1,G2,v` with `G = G1 & (x ~ T) & G2` and `x ↦ v ∈ s` and the value `v` has type `T` under `G1`.
- **[sto_binds_to_ctx_binds_raw]** (Lean: `sto_binds_to_ctx_binds_raw`) — If `wf_sto G s` and `x ↦ v ∈ s`, then there exist `G1,G2,T` with `G = G1 & (x ~ T) & G2` and `v` has type `T` under `G1`.
- **[invert_wf_sto_concat]** (Lean: `invert_wf_sto_concat`) — From `wf_sto (G1 & G2) s` decompose store as `s = s1 & s2` and `wf_sto G1 s1`.
- **[sto_unbound_to_ctx_unbound]** (Lean: `sto_unbound_to_ctx_unbound`) — If `x` fresh in store and `wf_sto G s`, then `x` fresh in `G`.
- **[ctx_unbound_to_sto_unbound]** (Lean: `ctx_unbound_to_sto_unbound`) — If `x` fresh in `G` and `wf_sto G s`, then `x` fresh in store.

## Typing inversions
- **[typing_implies_bound]** (Lean: `typing_implies_bound`) — From `ty_trm G (trm_var (avar_f x)) T`, deduce that `x` is bound in `G`.
- **[typing_bvar_implies_false]** (Lean: `typing_bvar_implies_false`) — A bound-variable term `trm_var (avar_b a)` cannot be well-typed.

## Extra Rec rules
- **[extra_bnd_rules]** (Lean: TODO) — Replace the binding `x ~ open_typ x S` by `x ~ typ_bnd S` across all judgments (`ty_trm`, `ty_def`, `ty_defs`, `subtyp`). Used to switch between recursive forms.

## Substitution — freshness and commuting
- **[subst_fresh_avar]** (Lean: TODO) — If `x ∉ fv_avar a` then substituting `x` by `y` in `a` is identity.
- **[subst_fresh_typ_dec]** (Lean: TODO) — Freshness lemma for types/declarations substitution.
- **[subst_fresh_trm_val_def_defs]** (Lean: TODO) — Freshness lemma for terms/values/defs/defs-list substitution.
- **[subst_fresh_typ]** (definition) — Projection for types from the previous lemma.
- **[subst_fresh_dec]** (definition) — Projection for declarations from the previous lemma.
- **[invert_fv_ctx_types_push]** (Lean: TODO) — If `x ∉ fv_ctx_types (G & z ~ T)`, then `x ∉ fv_typ T` and `x ∉ fv_ctx_types G`.
- **[subst_fresh_ctx]** (Lean: TODO) — If `x ∉ fv_ctx_types G`, then `subst_ctx x y G = G`.
- **[subst_open_commute_avar]** (Lean: TODO) — Substitution commutes with opening on `avar`.
- **[subst_open_commute_typ_dec]** (Lean: TODO) — Substitution commutes with opening on `typ`/`dec` (mutual).
- **[subst_open_commute_typ]** (Lean: TODO) — Shorthand for types.
- **[subst_open_commute_dec]** (Lean: TODO) — Shorthand for declarations.
- **[subst_open_commute_trm_val_def_defs]** (Lean: TODO) — Substitution commutes with opening on `trm`/`val`/`def`/`defs` (mutual).
- **[subst_open_commute_trm]** (Lean: TODO) — Shorthand for terms.
- **[subst_open_commute_val]** (Lean: TODO) — Shorthand for values.
- **[subst_open_commute_defs]** (Lean: TODO) — Shorthand for defs list.

## Substitution — intro and undo
- **[subst_intro_trm]** (Lean: TODO) — If `x ∉ fv_trm t`, then `open_trm u t = subst_trm x u (open_trm x t)`.
- **[subst_intro_val]** (Lean: TODO) — Intro lemma for `val`.
- **[subst_intro_defs]** (Lean: TODO) — Intro lemma for `defs`.
- **[subst_intro_typ]** (Lean: TODO) — Intro lemma for `typ`.
- **[subst_intro_dec]** (Lean: TODO) — Intro lemma for `dec`.
- **[subst_undo_avar]** (Lean: TODO) — Undo a pair of substitutions on `avar` under freshness.
- **[subst_undo_typ_dec]** (Lean: TODO) — Undo a pair of substitutions on `typ`/`dec` under freshness.
- **[subst_undo_trm_val_def_defs]** (Lean: TODO) — Undo a pair of substitutions on `trm`/`val`/`def`/`defs` under freshness.

## Typing (selected key rules shown in `Def.lean`)
- `ty_trm/ty_def/ty_defs` — Standard DOT typing rules including `all`, `let`, `rec`, and records.
- `subtyp` — Subtyping with `top`, `bot`, conjunction, record field/type, selection rules (both general and tight), and `all`.
- `wf_sto` — Well-formed store definition.

## Operational semantics
- `red` — Small-step reduction rules for selection, application, and let-binding.

## Notes
- This glossary will be extended to include the remaining lemmas in `Dot_top_bot.v` as scaffolding proceeds. The Lean `Proof.lean` currently contains statements for weakening, store well-formedness facts, store-context relations, and basic typing inversions; further substitution and member-related lemmas can be added following the same naming.
