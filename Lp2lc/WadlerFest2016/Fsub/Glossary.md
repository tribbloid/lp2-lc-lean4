# Glossary for System F<: (Fsub) — Preservation and Progress

This glossary explains every lemma/theorem in `Lp2lc_coq/Active/Fsub.v`, with a short purpose. Where applicable, the corresponding Lean name in `Lp2lc/Active/Fsub/Proof.lean` is noted.

Legend:
- Coq name: the identifier as used in `Fsub.v`.
- Lean name: the corresponding `theorem` name in Lean (if present).
- Meaning: concise purpose/role in the development.

## Substitutions on types (in types)
- **[open_tt_rec_type_core]** (Lean: `open_tt_rec_type_core`) — Core commuting lemma: if opening at `j` then opening at `i` leaves structure unchanged, the body equals opening at `i`. Used to prove opening is inert on well-formed objects.
- **[open_tt_rec_type]** (Lean: `open_tt_rec_type`) — Opening a well-formed type is identity. Shows locally closed types are stable under opening free index 0 (cofinite machinery).
- **[subst_tt_fresh]** (Lean: `subst_tt_fresh`) — Substituting a type variable not free in `T` leaves `T` unchanged.
- **[subst_tt_open_tt_rec]** (Lean: `subst_tt_open_tt_rec`) — Type substitution distributes over type opening (de Bruijn indices) at any depth `n`.
- **[subst_tt_open_tt]** (Lean: `subst_tt_open_tt`) — Shorthand of the above for depth `0` / `open_tt`.
- **[subst_tt_open_tt_var]** (Lean: `subst_tt_open_tt_var`) — Substitution commutes with opening by a distinct fresh type variable.
- **[subst_tt_intro]** (Lean: `subst_tt_intro`) — Opening a body with a type `U` equals opening with a fresh var then substituting that var by `U`.

## Substitutions on types (in terms)
- **[open_te_rec_term_core]** (Lean: `open_te_rec_term_core`) — Opening a term with a term variable then with a type variable commutes in the core sense.
- **[open_te_rec_type_core]** (Lean: `open_te_rec_type_core`) — Opening a term with types at distinct indices commutes.
- **[open_te_rec_term]** (Lean: `open_te_rec_term`) — Opening a locally closed term with a type is identity.
- **[subst_te_fresh]** (Lean: `subst_te_fresh`) — Substituting a type variable not free in a term leaves the term unchanged.
- **[subst_te_open_te]** (Lean: `subst_te_open_te`) — Type substitution in terms distributes over type opening in terms.
- **[subst_te_open_te_var]** (Lean: `subst_te_open_te_var`) — Commutes with opening by a distinct fresh type variable.
- **[subst_te_intro]** (Lean: `subst_te_intro`) — Opening a term body with a type equals opening with fresh type var then substituting that var.

## Substitutions on terms (in terms)
- **[open_ee_rec_term_core]** (Lean: `open_ee_rec_term_core`) — Opening with a term at `j` then at `i ≠ j` commutes to opening at `i` on the body.
- **[open_ee_rec_type_core]** (Lean: `open_ee_rec_type_core'`) — Opening by a type, then by a term, commutes at the core level.
- **[open_ee_rec_term]** (Lean: `open_ee_rec_term`) — Opening a locally closed term with a term is identity.
- **[subst_ee_fresh]** (Lean: `subst_ee_fresh`) — Substituting a term variable not free in `e` leaves `e` unchanged.
- **[subst_ee_open_ee]** (Lean: `subst_ee_open_ee`) — Term substitution distributes over term opening.
- **[subst_ee_open_ee_var]** (Lean: `subst_ee_open_ee_var`) — Commutes with opening by a distinct fresh term variable.
- **[subst_ee_intro]** (Lean: `subst_ee_intro`) — Opening a term body with a term equals opening with a fresh variable then substituting that variable by the term.
- **[subst_te_open_ee_var]** (Lean: `subst_te_open_ee_var`) — Type substitution in terms commutes with opening by a term variable.
- **[subst_ee_open_te_var]** (Lean: `subst_ee_open_te_var`) — Term substitution commutes with opening by a type variable.

## Substitutions preserve local closure
- **[subst_tt_type]** (Lean: `subst_tt_type`) — If `T,P` are types, then `subst_tt Z P T` is a type. Closure preserved under type substitution.
- **[subst_te_term]** (Lean: `subst_te_term`) — If `e` is a term and `P` a type, then `subst_te Z P e` is a term.
- **[subst_ee_term]** (Lean: `subst_ee_term`) — If `e1,e2` are terms, then `subst_ee Z e2 e1` is a term.

## Well-formedness of types in environments
- **[wft_type]** (Lean: `wft_type`) — Well-formed in env implies locally closed (`type`).
- **[wft_weaken]** (Lean: `wft_weaken`) — WFT is stable under environment weakening.
- **[wft_narrow]** (Lean: `wft_narrow`) — Narrowing a bound `X <: V` to `X <: U` (with `U` below `V`) preserves WFT.
- **[wft_strengthen]** (Lean: `wft_strengthen`) — Removing an unrelated term binding preserves WFT.
- **[wft_subst_tb]** (Lean: `wft_subst_tb`) — WFT preserved under type substitution inside the environment block `map (subst_tb Z P) F`.
- **[wft_open]** (Lean: `wft_open`) — Opening a `∀`-type with a well-formed type yields a well-formed type.

## Relations between well-formed env and well-formed types
- **[ok_from_okt]** (Lean: `ok_from_okt`) — From structured env well-formedness (`okt`) derive raw `ok` (no dup keys).
- **[wft_from_env_has_sub]** (Lean: `wft_from_env_has_sub`) — If `X <: U` is bound in `E` and `okt E`, then `wft E U`.
- **[wft_from_env_has_typ]** (Lean: `wft_from_env_has_typ`) — If `x : U` is bound in `E` and `okt E`, then `wft E U`.
- **[wft_from_okt_typ]** (Lean: `wft_from_okt_typ`) — From `okt (E & x : T)` get `wft E T`.
- **[wft_from_okt_sub]** (Lean: `wft_from_okt_sub`) — From `okt (E & X <: T)` get `wft E T`.
- **[wft_weaken_right]** (Lean: `wft_weaken_right`) — A convenient right-weakening instance for WFT.

## Environment substitution freshness facts
- **[notin_fv_tt_open]** (Lean: `notin_fv_tt_open`) — If `X ∉ fv_tt (T open_tt_var Y)` then `X ∉ fv_tt T`.
- **[notin_fv_wf]** (Lean: `notin_fv_wf`) — If `wft E T` and `X # E`, then `X ∉ fv_tt T`.
- **[map_subst_tb_id]** (Lean: `map_subst_tb_id`) — Substituting a fresh type variable through an `okt` env leaves the env unchanged.

## Environment well-formedness (okt) — inversions, narrowing, strengthening, substitution
- **[okt_push_inv]** (Lean: `okt_push_inv`) — Pushing any binding implies it is either `bind_sub T` or `bind_typ T` for some `T`.
- **[okt_push_sub_inv]** (Lean: `okt_push_sub_inv`) — Invert `okt (E & X <: T)`: get `okt E`, `wft E T`, freshness.
- **[okt_push_sub_type]** (Lean: `okt_push_sub_type`) — From `okt (E & X <: T)` derive `type T`.
- **[okt_push_typ_inv]** (Lean: `okt_push_typ_inv`) — Invert `okt (E & x : T)`: get `okt E`, `wft E T`, freshness.
- **[okt_push_typ_type]** (Lean: `okt_push_typ_type`) — From `okt (E & x : T)` derive `type T`.
- **[okt_narrow]** (Lean: `okt_narrow`) — Narrowing in `okt` preserves `okt`.
- **[okt_strengthen]** (Lean: `okt_strengthen`) — Strengthening in `okt` preserves `okt`.
- **[okt_subst_tb]** (Lean: `okt_subst_tb`) — `okt` preserved under type substitution through a suffix environment.

## Regularity lemmas
- **[sub_regular]** (Lean: `sub_regular`) — If `sub E S T` then `okt E`, `wft E S`, and `wft E T`.
- **[typing_regular]** (Lean: `typing_regular`) — If `typing E e T` then `okt E`, `term e`, and `wft E T`.
- **[value_regular]** (Lean: `value_regular`) — A value is always a locally closed term.
- **[red_regular]** (Lean: `red_regular`) — One-step reduction preserves local closure on source and target.

## Subtyping — structure lemmas
- **[sub_reflexivity]** (Lean: `sub_reflexivity`) — Subtyping is reflexive on well-formed types under well-formed envs.
- **[sub_weakening]** (Lean: `sub_weakening`) — Subtyping is preserved by environment weakening.
- **[sub_narrowing_aux]** (Lean: `sub_narrowing_aux`) — Auxiliary lemma: subtyping preserved when narrowing a type variable bound, assuming transitivity on the bound type.
- **[sub_transitivity]** (Lean: `sub_transitivity`) — Subtyping is transitive (key meta-property driving narrowing and substitution through subtyping).
- **[sub_narrowing]** (Lean: `sub_narrowing`) — Subtyping preserved under narrowing via `sub_transitivity`.
- **[sub_through_subst_tt]** (Lean: `sub_through_subst_tt`) — Subtyping preserved through type substitution in both the environment suffix and the types.

## Typing — weakening, narrowing, substitution
- **[typing_weakening]** (Lean: `typing_weakening`) — Typing is preserved by environment weakening.
- **[sub_strengthening]** (Lean: `sub_strengthening`) — Subtyping unaffected by removing an unrelated term binding; used inside typing proofs.
- **[typing_narrowing]** (Lean: `typing_narrowing`) — Typing preserved under narrowing a type variable bound.
- **[typing_through_subst_ee]** (Lean: `typing_through_subst_ee`) — Term substitution preserves typing (standard substitution lemma for terms).
- **[typing_through_subst_te]** (Lean: `typing_through_subst_te`) — Type substitution preserves typing (standard substitution lemma for types).

## Preservation — inversion lemmas and main theorem
- **[typing_inv_abs]** (Lean: `typing_inv_abs`) — Invert typing of `λ`: from `typing E (abs S1 e1) T` and `T <: U1→U2`, derive `U1 <: S1` and a body typing `S2` with `S2 <: U2`.
- **[typing_inv_tabs]** (Lean: `typing_inv_tabs`) — Invert typing of `Λ`: from `typing E (tabs S1 e1) T` and `T <: ∀U1.U2`, derive `U1 <: S1` and body typing under `X <: U1` with appropriate subtype.
- **[preservation_result]** (Lean: `preservation_result`) — If `typing E e T` and `red e e'`, then `typing E e' T`.
  - Why it entails soundness: Combined with progress, preservation ensures that evaluation never gets stuck and types are invariant across steps, which is half of type soundness.

## Progress — canonical forms and main theorem
- **[canonical_form_abs]** (Lean: `canonical_form_abs`) — If a value has arrow type under empty env, it must be a term abstraction.
- **[canonical_form_tabs]** (Lean: `canonical_form_tabs`) — If a value has universal type under empty env, it must be a type abstraction.
- **[progress_result]** (Lean: `progress_result`) — If `typing empty e T` then either `e` is a value or it can take a reduction step.
  - Why it entails soundness: Together with preservation, progress implies that well-typed closed terms cannot get stuck; hence the language is type-safe.
## Lean-only helper theorems
- **[binds_weaken]** (Lean: `binds_weaken`) — Binding lookup is preserved by environment weakening from `E ++ G` to `E ++ F ++ G` (`Lp2lc/Active/Fsub/Proof.lean`).
- **[okt_empty]** (Lean: `okt_empty`) — The empty environment is well-formed (`okt`).

## Notes
- The above grouping mirrors section headers in `Fsub.v` to clarify roles.
- Lean counterparts in `Proof.lean` largely mirror Coq names; differences (e.g., a trailing `'` in `open_ee_rec_type_core'`) are noted where applicable.
