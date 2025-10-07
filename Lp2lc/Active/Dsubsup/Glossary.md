# Dsubsup (D<:>) — Theorem Glossary

Source files:
- Coq: `Lp2lc_coq/Active/Dsubsup.v`
- Lean aggregator: `Lp2lc/Active/Dsubsup/Proof.lean`

Conventions:
- Each entry lists the Coq theorem/lemma name and its Lean counterpart(s).
- Briefly states the meaning/purpose. Primary theorems explain their role in soundness.

## Primary Theorems (Soundness)

- Name: `preservation` (Coq definition) → `preservation_result` (Lean)
  - Meaning: If `typing empty e T` and `red e e'`, then `typing empty e' T`.
  - Soundness: Guarantees types are invariant under evaluation; no type changes during computation.

- Name: `progress` (Coq definition) → `progress_result` (Lean)
  - Meaning: If `typing empty e T`, then either `value e` or there exists `e'` such that `red e e'`.
  - Soundness: Well-typed closed terms do not get stuck; they are values or can take a reduction step.

## Opening and Substitution Basics

- Name: `open_rec_lc_core` → `open_rec_lc_core_T`, `open_rec_lc_core_E`
  - Meaning: Opening with distinct indices commutes; opening a locally closed object is stable.

- Name: `open_rec_lc` → `open_rec_lc_T`, `open_rec_lc_E`
  - Meaning: For locally closed types/terms, opening at any index is identity.

- Name: `open_t_var_type` → `open_t_var_type`
  - Meaning: Opening a well-formed type with a fresh variable yields the same type.

- Name: `subst_fresh` → `subst_fresh_T`, `subst_fresh_E`
  - Meaning: Substituting a variable not free in a type/term is a no-op.

- Name: `subst_open_rec` → `subst_open_rec_T`, `subst_open_rec_E`
  - Meaning: Substitution distributes over de Bruijn opening operations.

- Name: `subst_t_open_t` → `substT_openT`
  - Meaning: Substitution distributes over type opening (`open_t`).

- Name: `subst_e_open_e` → `substE_openE`
  - Meaning: Substitution distributes over term opening (`open_e`).

- Name: `subst_t_open_t_var` → `substT_openT_var`
  - Meaning: Substitution commutes with opening by a distinct variable on types.

- Name: `subst_e_open_e_var` → `substE_openE_var`
  - Meaning: Substitution commutes with opening by a distinct variable on terms.

- Name: `subst_t_intro` → `substT_intro`
  - Meaning: Opening a body with a term equals opening with a fresh var followed by substitution.

- Name: `subst_e_intro` → `substE_intro`
  - Meaning: Term-level variant of the above introduction lemma for substitution and opening.

- Name: `subst_lc` → `subst_lc_T`, `subst_lc_E`
  - Meaning: Substitution preserves local closure for types and terms.

- Name: `subst_t_type` → `substT_type`
  - Meaning: If `type T` and `term u`, then `type (subst_t z u T)`; a corollary of substitution preserving closure.

- Name: `subst_e_term` → `substE_term`
  - Meaning: If `term e1` and `term e2`, then `term (subst_e z e2 e1)`; corollary for terms.

- Name: `subst_e_value` → `substE_value`
  - Meaning: Substitution preserves values (abstractions and mem-terms remain values after substitution).

- Name: `value_is_term` → `value_is_term`
  - Meaning: Every value is a locally closed term.

## Well-Formedness (Types/Terms) and Environment Basics

- Name: `wf_lc` → `wft_lcT`, `wfe_lcE`
  - Meaning: Well-formedness in an environment implies local closure of types/terms.

- Name: `wft_type` → `wft_type`
  - Meaning: Specialization: `wft E T` implies `type T`.

- Name: `wfe_term` → `wfe_term`
  - Meaning: Specialization: `wfe E e` implies `term e`.

- Name: `ok_from_okt` → `ok_from_okt`
  - Meaning: A well-formed environment (`okt`) has no duplicate keys (`ok`).

- Name: `wft_from_env_has` → `wft_from_env_has`
  - Meaning: From `okt E` and `binds x U E`, deduce `wft E U`.

- Name: `wft_from_okt` → `wft_from_okt`
  - Meaning: From `okt (E & x ~ T)` obtain `wft E T`.

- Name: `wft_weaken_right` → `wft_weaken_right`
  - Meaning: Weakening on the right preserves `wft`.

- Name: `okt_push_inv` → `okt_push_inv`
  - Meaning: Inversion for `okt (E & x ~ T)`: yields `okt E`, `wft E T`, and freshness of `x` in `E`.

- Name: `okt_push_type` → `okt_push_type`
  - Meaning: From `okt (E & x ~ T)` get that `type T` holds.

- Name: `okt_narrow` → `okt_narrow`
  - Meaning: Narrowing a binding in a well-formed environment preserves `okt`.

- Name: `okt_subst` → `okt_subst`, `okt_subst1`
  - Meaning: Substituting a fresh name in an `okt` environment preserves `okt` (with mapped types).

## Free Variables, Opening, and Freshness

- Name: `notin_fv_open_rec` → `notin_fv_open_rec_T`, `notin_fv_open_rec_E`
  - Meaning: Freshness is preserved when moving from an opened object back to its body.

- Name: `notin_fv_t_open` → `notin_fv_t_open`
  - Meaning: If `x` not in `fv_t (T open_t_var y)`, then `x` not in `fv_t T`.

- Name: `notin_fv_e_open` → `notin_fv_e_open`
  - Meaning: If `x` not in `fv_e (e open_e_var y)`, then `x` not in `fv_e e`.

- Name: `notin_fv_wf_rec` → `notin_fv_wf_rec_T`, `notin_fv_wf_rec_E`
  - Meaning: Variables fresh in an environment are not free in well-formed objects.

- Name: `notin_fv_wf` → `notin_fv_wf`
  - Meaning: Specialization of the above to types.

- Name: `map_subst_id` → `map_subst_id`
  - Meaning: Mapping substitution of a fresh variable across an `okt` environment leaves it unchanged.

## Weakening, Narrowing, Substitution (Judgments)

- Name: `wf_weaken` → `wf_weaken_T`, `wf_weaken_E`
  - Meaning: Type/term well-formedness is preserved under environment weakening.

- Name: `wft_weaken` → `wft_weaken`
  - Meaning: `wft (E & G) T` implies `wft (E & F & G) T` under `ok`.

- Name: `wft_weaken_empty` → `wft_weaken_empty`
  - Meaning: From `wft empty T` and `ok E`, deduce `wft E T`.

- Name: `wfe_weaken` → `wfe_weaken`
  - Meaning: Term well-formedness preserved under environment weakening.

- Name: `wfe_weaken_empty` → `wfe_weaken_empty`
  - Meaning: From `wfe empty e` and `ok E`, deduce `wfe E e`.

- Name: `wf_narrow` → `wf_narrow_T`, `wf_narrow_E`
  - Meaning: Narrowing a binding type in an environment preserves well-formedness of types/terms.

- Name: `wft_narrow` → `wft_narrow`
  - Meaning: Specialization: `wft` preserved by narrowing.

- Name: `wf_subst` → `wf_subst_T`, `wf_subst_E`
  - Meaning: Substitution through an environment binding preserves well-formedness of types/terms.

- Name: `wft_subst` → `wft_subst`
  - Meaning: Specialization of `wf_subst` to types.

- Name: `wft_subst1` → `wft_subst1`
  - Meaning: One-binding variant of substitution preservation for `wft`.

- Name: `wft_subst_empty` → `wft_subst_empty`
  - Meaning: Substitution into a singleton environment yields `wft [] (subst_t ...)`.

## Regularity of Relations (Sub, Has, Typing, Red)

- Name: `sub_regular` → `sub_regular`
  - Meaning: If `sub E S T` then `okt E`, `wft E S`, and `wft E T`.

- Name: `has_regular` → `has_regular`
  - Meaning: If `has E p T` then `okt E`, `wft E (typ_sel p)`, and `wft E T`.

- Name: `has_regular_e` → `has_regular_e`
  - Meaning: From `has E p T`, deduce `(value p ∨ p is a variable)` and `wfe E p`.

- Name: `typing_regular` → `typing_regular`
  - Meaning: If `typing E e T` then `okt E`, `wfe E e`, and `wft E T`.

- Name: `value_regular` → `value_regular`
  - Meaning: Values are locally closed terms.

- Name: `red_regular` → `red_regular`
  - Meaning: Single-step reduction relates locally closed terms.

- Name: `wft_open` → `wft_open`
  - Meaning: Opening a universally quantified type with a well-formed argument yields a well-formed type.

## Subtyping and Typing Structural Properties

- Name: `sub_reflexivity` → `sub_reflexivity`
  - Meaning: Every well-formed type is a subtype of itself.

- Name: `sub_weakening` → `sub_weakening`
  - Meaning: Subtyping is preserved under environment weakening.

- Name: `sub_has_weakening` → `sub_has_weakening_pair`
  - Meaning: Packaged weakening lemmas for both `sub` and `has`.

- Name: `sub_weakening1` → `sub_weakening1`
  - Meaning: Subtyping preserved when extending environment by arbitrary middle segment.

- Name: `sub_weakening_empty` → `sub_weakening_empty`
  - Meaning: From `sub [] S T` and `okt E`, deduce `sub E S T`.

- Name: `has_weakening` → `has_weakening`
  - Meaning: `has` judgments preserved under environment weakening.

- Name: `has_weakening1` → `has_weakening1`
  - Meaning: `has E p T` implies `has (E ++ F ++ G) p T` under `okt`.

- Name: `has_weakening_empty` → `has_weakening_empty`
  - Meaning: From `has [] p T` and `okt E`, deduce `has E p T`.

- Name: `sub_has_narrowing_aux` → `sub_has_narrowing_aux`
  - Meaning: Auxiliary narrowing for `sub` and `has` through a single binding.

- Name: `sub_narrowing` → `sub_narrowing`
  - Meaning: If `sub E P Q` then replacing `(z,Q)` with `(z,P)` in a larger env preserves a `sub` judgment.

- Name: `sub_narrowing_empty` → `sub_narrowing_empty`
  - Meaning: Empty-environment instance of narrowing.

- Name: `typing_weakening` → `typing_weakening`
  - Meaning: Typing preserved under environment weakening.

- Name: `typing_narrowing` → `typing_narrowing`
  - Meaning: Typing preserved when narrowing a specific binding.

- Name: `typing_narrowing_empty` → `typing_narrowing_empty`
  - Meaning: Empty-environment instance of typing narrowing.

- Name: `typing_through_subst` → `typing_through_subst`
  - Meaning: Typing is preserved through substitution of a variable by a value with its type.

## Canonical Forms and Possible Types

- Name: `has_empty_value` → `has_empty_value`
  - Meaning: In the empty environment, any `has [] p T` means `p` is a value.

- Name: `psub_sub` → `psub_sub`
  - Meaning: Declarative pseudo-subtyping `psub` implies algorithmic subtyping `sub` in empty env.

- Name: `possible_types_value` → `possible_types_value`
  - Meaning: If `possible_types n p T`, then `p` is a value.

- Name: `possible_types_wfe` → `possible_types_wfe`
  - Meaning: If `possible_types n p T`, then `wfe [] p`.

- Name: `possible_types_wft` → `possible_types_wft`
  - Meaning: If `possible_types n p T`, then `wft [] T`.

- Name: `has_empty_var_false` → `has_empty_var_false`
  - Meaning: Variables cannot have types in an empty environment via `has`.

- Name: `possible_types_closure_psub` → `possible_types_closure_psub`
  - Meaning: `possible_types` is closed under pseudo-subtyping step on types.

- Name: `psub_reflexivity` → `psub_reflexivity`
  - Meaning: Any well-formed closed type is `psub` to itself.

- Name: `sub_psub_aux` → `sub_psub_aux_sub`, `sub_psub_aux_has`
  - Meaning: From empty-env `sub/has`, derive corresponding `psub/possible_types` witnesses.

- Name: `sub_psub` → `sub_psub`
  - Meaning: Empty-environment `sub` implies `psub`.

- Name: `possible_types_closure` → `possible_types_closure`
  - Meaning: `possible_types` is closed under empty-environment subtyping on result type.

- Name: `possible_types_typing` → `possible_types_typing`
  - Meaning: From `typing [] v T` and `value v`, get `possible_types 1 v T`.

## Canonical Form Inversions and Preservation Helpers

- Name: `typing_inv_abs` → `typing_inv_abs`
  - Meaning: Inversion of `typing [] (abs S1 e1) T` against `sub [] T (all U1 U2)` yields parameter subtyping and body typing.

- Name: `typing_through_subst1` → `typing_through_subst1`
  - Meaning: One-binding specialization of typing through substitution in empty environment.

- Name: `value_red_contra` → `value_red_contra`
  - Meaning: Values cannot reduce in one step.

- Name: `canonical_form_abs` → `canonical_form_abs`
  - Meaning: If `value t` and `typing [] t (all U1 U2)`, then `t` is an abstraction.

- Name: `canonical_form_mem` → `canonical_form_mem`
  - Meaning: If `value t` and `typing [] t (mem b T)`, then `t` is a memory/type member term.
