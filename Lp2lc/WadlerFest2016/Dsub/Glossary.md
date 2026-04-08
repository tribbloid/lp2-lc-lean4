# Dsub Theorem Glossary

This glossary explains the theorems and lemmas in `Lp2lc_coq/Active/Dsub.v` and their Lean counterparts in `Lp2lc/Active/Dsub/Proof.lean`.
For split ports, Lean uses `_t` (type) and `_e` (term) suffixes.

- Coverage
  - [x] All Coq lemmas/theorems from `Lp2lc_coq/Active/Dsub.v`
  - [x] All Lean scaffolds from `Lp2lc/Active/Dsub/Proof.lean`

## Core syntax: opening and substitution

- **`open_rec_lc_core` / `open_rec_lc_core_t` / `open_rec_lc_core_e`**
  - Full name: Opening recursion locally closed core
  - Meaning: If two openings at distinct indices coincide, the original object equals its opening at the second index. Basis for opening-commutation.

- **`open_rec_lc` / `open_rec_lc_t` / `open_rec_lc_e`**
  - Full name: Opening preserves locally closed forms
  - Meaning: Opening a locally closed type/term yields the same object (no effect).

- **`open_t_var_type`**
  - Full name: Opening a type with a variable is a no-op for well-formed types
  - Meaning: For `type T`, `open_t T (trm_fvar x) = T`.

- **`subst_fresh` / `subst_fresh_t` / `subst_fresh_e`**
  - Full name: Substitution for a fresh variable is identity
  - Meaning: If a variable is not free, substituting it does not change the object.

- **`subst_open_rec` / `subst_open_rec_t` / `subst_open_rec_e`**
  - Full name: Substitution distributes over opening
  - Meaning: Substitution commutes with opening (both for types and terms).

- **`subst_t_open_t` / `subst_e_open_e`**
  - Full name: Substitution over top-level opening
  - Meaning: Special cases of `subst_open_rec` at index 0.

- **`subst_t_open_t_var` / `subst_e_open_e_var`**
  - Full name: Substitution and opening with distinct variable commute
  - Meaning: If `x ≠ y`, substitution w.r.t. `x` commutes with opening w.r.t. `y`.

- **`subst_t_intro` / `subst_e_intro`**
  - Full name: Opening equals substitution after choosing a fresh variable
  - Meaning: Opening with `u` equals substituting `u` for a fresh `x` after opening with `x`.

## Substitution preserves closure

- **`subst_lc` / `subst_lc_t` / `subst_lc_e`**
  - Full name: Substitution preserves local closure
  - Meaning: If bodies are locally closed, substituting a term preserves `type`/`term`.

- **`subst_t_type` / `subst_e_term`**
  - Full name: Substitution preserves well-formedness (corollaries)
  - Meaning: Immediate corollaries of `subst_lc` for types and terms.

- **`subst_e_value`**
  - Full name: Substitution preserves values
  - Meaning: Substituting into a value yields a value.

- **`value_is_term` / `value_regular`**
  - Full name: Values are terms
  - Meaning: Any value is a locally closed term.

## Well-formedness of types/terms and environments

- **`wf_lc` / `wf_lc_t` / `wf_lc_e`**
  - Full name: Well-formed implies locally closed
  - Meaning: `wft E T → type T` and `wfe E e → term e`.

- **`wft_type` / `wfe_term`**
  - Full name: Projections from `wf_lc`
  - Meaning: Convenience lemmas deriving `type`/`term` from `wft`/`wfe`.

- **`wf_weaken` (mutual) / `wft_weaken` / `wfe_weaken` / `wft_weaken_right` / `wft_weaken_empty` / `wfe_weaken_empty`**
  - Full name: Weakening for well-formedness
  - Meaning: Extending environments preserves `wft`/`wfe` under `ok`.

- **`wf_narrow` (mutual) / `wft_narrow`**
  - Full name: Narrowing for well-formedness
  - Meaning: Replacing a bound type with a subtype preserves well-formedness.

- **`wf_subst` (mutual) / `wft_subst` / `wft_subst1` / `wft_subst_empty`**
  - Full name: Substitution preserves well-formedness
  - Meaning: Substituting through environments preserves `wft`/`wfe`.

- **`wft_open`**
  - Full name: Opening an ∀-type body preserves well-formedness
  - Meaning: If `wft E (∀ T1. T2)`, then `wft E (open_t T2 u)` for a well-formed `u`.

- **`ok_from_okt`**
  - Full name: `okt` implies `ok`
  - Meaning: Structural well-formedness implies no duplicate keys.

- **`wft_from_env_has`**
  - Full name: Binding implies well-formed bound type
  - Meaning: From `okt E` and `binds x U E`, get `wft E U`.

- **`wft_from_okt`**
  - Full name: Extract binding’s type is well-formed
  - Meaning: From `okt (E & x ~ T)` infer `wft E T`.

- **`okt_push_inv` / `okt_push_type`**
  - Full name: Inversion and type of a pushed env entry
  - Meaning: Decompose `okt (E & x ~ T)`; also, `type T` under `okt`.

- **`okt_narrow` / `okt_strengthen` (Lean) / `okt_subst` / `okt_subst1`**
  - Full name: Environment transformations preserve `okt`
  - Meaning: Narrowing/strengthening/substitution keep environments well-formed.

- **`binds_weaken` (Lean)**
  - Full name: Weakening preserves lookup
  - Meaning: If a binding is found in `E ++ G`, it is found in `E ++ F ++ G`.

## Free variables and freshness

- **`notin_fv_open_rec` / `notin_fv_open_rec_t` / `notin_fv_open_rec_e`**
  - Full name: Freshness preserved through opening (indices)
  - Meaning: If `x` not in free vars after opening, then `x` not in original.

- **`notin_fv_t_open` / `notin_fv_e_open`**
  - Full name: Freshness preserved through top-level opening
  - Meaning: Special cases for `open_t`/`open_e`.

- **`notin_fv_wf_rec` / `notin_fv_wf` / `notin_fv_wf_t` / `notin_fv_wf_e`**
  - Full name: Free-variable bounds from well-formedness
  - Meaning: Fresh variables w.r.t. environment do not appear free in objects.

- **`map_subst_id` (Coq) / `map_subst_t_id` (Lean)**
  - Full name: Substitution mapping leaves env unchanged when variable is fresh
  - Meaning: Mapping `subst_t z u` over an env with `z ∉ dom` is the identity.

## Regularity lemmas

- **`sub_has_regular` / `sub_regular` / `has_regular` / `has_regular_e`**
  - Full name: Regularity of subtyping/has
  - Meaning: From `sub`/`has`, derive `okt E` and `wft` of involved types (and that the subject is a value or variable for `has`).

- **`typing_regular`**
  - Full name: Regularity of typing
  - Meaning: From `typing E e T`, derive `okt E`, `wfe E e`, and `wft E T`.

- **`red_regular`**
  - Full name: Regularity of reduction
  - Meaning: One-step reduction relates locally closed terms.

## Subtyping: structural properties

- **`sub_reflexivity`**
  - Full name: Reflexivity of subtyping
  - Meaning: Any well-formed type is a subtype of itself.

- **`sub_has_weakening` / `sub_weakening` / `sub_weakening1` / `sub_weakening_empty`**
  - Full name: Weakening for subtyping (and `has`)
  - Meaning: Extending environments preserves `sub` and `has` judgments.

- **`has_weakening` / `has_weakening1` / `has_weakening_empty`**
  - Full name: Weakening for `has`
  - Meaning: As above, specialized to `has`.

- **`sub_has_narrowing_aux` / `sub_has_narrowing_aux_t` / `sub_has_narrowing_aux_e`**
  - Full name: Narrowing for subtyping and `has`
  - Meaning: Replacing a variable’s bound type with a subtype preserves `sub`/`has`.

- **`sub_narrowing` / `sub_narrowing_empty`**
  - Full name: Narrowing instances
  - Meaning: Direct corollaries of the auxiliary narrowing lemma.

## Subtyping and typing through substitution

- **`has_value_var`**
  - Full name: Subjects of `has` are values or variables
  - Meaning: From `has E u T`, conclude `u` is a value or a free variable.

- **`var_typing_has` / `val_typing_has`**
  - Full name: `has` from typing for variables/values
  - Meaning: A typed variable/value has the corresponding `has` judgment.

- **`sub_has_through_subst` / `sub_has_through_subst_t` / `sub_has_through_subst_e`**
  - Full name: Substitution preserves `sub`/`has`
  - Meaning: Substituting a well-typed term for a variable preserves `sub` and `has`.

- **`typing_weakening`**
  - Full name: Weakening for typing
  - Meaning: Extending the environment preserves typing.

- **`typing_narrowing` / `typing_narrowing_empty`**
  - Full name: Narrowing for typing
  - Meaning: Replacing a bound type with a subtype preserves typing.

- **`typing_through_subst` / `typing_through_subst1`**
  - Full name: Typing preserved by substitution
  - Meaning: Substituting a value (or closed well-typed term) preserves typing.

## Auxiliary relations: `psub` and `possible_types`

- **`psub` (inductive) / `psub_sub` / `psub_reflexivity`**
  - Full name: Pseudo-subtyping and its link to `sub`
  - Meaning: A closed-style subtyping used in progress/preservation; it implies `sub` and is reflexive on well-formed types.

- **`possible_types` (inductive)**
  - Full name: Possible types for a value/term
  - Meaning: Describes canonical shapes of types inhabitable by values/terms.

- **`has_empty_value` / `has_empty_var_false`**
  - Full name: Shape of subjects in empty environments
  - Meaning: In empty env, `has [] p T` forces `p` to be a value; variables cannot have `has` at empty env.

- **`possible_types_value` / `possible_types_wfe` / `possible_types_wft`**
  - Full name: Regularity of `possible_types`
  - Meaning: From `possible_types`, derive that subjects are values and objects well-formed.

- **`possible_types_closure_psub` / `possible_types_closure`**
  - Full name: Closure of `possible_types` under (pseudo-)subtyping
  - Meaning: `possible_types` is closed under `psub` and under `sub` at empty env.

- **`sub_psub_aux` / `sub_psub` / `sub_psub_aux_t` / `sub_psub_aux_e`**
  - Full name: From `sub` at empty env to `psub`/`possible_types`
  - Meaning: Bridges environment-free subtyping with `psub` and `possible_types`.

- **`possible_types_typing`**
  - Full name: From typing and value to possible types
  - Meaning: If `typing [] v T` and `value v`, then `possible_types 1 v T`.

- **`typing_inv_abs`**
  - Full name: Inversion for abstractions
  - Meaning: From `typing [] (abs S1 e1) T` and `sub [] T (∀ U1. U2)`, get parameter subtyping and body typing obligations.

- **`canonical_form_abs` / `canonical_form_mem`**
  - Full name: Canonical forms lemmas
  - Meaning: If a value has a function (or member) type, it must be a `trm_abs` (or `trm_mem`).

## Preservation and Progress (Soundness)

- **`value_red_contra`**
  - Full name: Values do not reduce
  - Meaning: No reduction step starts from a value.

- **`preservation_result`**
  - Full name: Preservation
  - Meaning: If `typing [] e T` and `red e e'`, then `typing [] e' T`.
  - Why soundness: Along with Progress, it ensures types are invariant under computation, preventing type errors during execution.

- **`progress_result`**
  - Full name: Progress
  - Meaning: If `typing [] e T`, then `e` is a value or can take a step.
  - Why soundness: Together with Preservation, ensures a well-typed closed program does not get stuck.

- **`preservation` / `progress` (definitions)**
  - Full name: Statements of preservation and progress
  - Meaning: Specifications used by the above results to express soundness.

## Lean-specific scaffolds mapped to Coq

- Open/subst splits: `open_rec_lc_core_t/e`, `open_rec_lc_t/e`, `subst_open_rec_t/e`, `subst_lc_t/e` mirror Coq mutual lemmas.
- Env helpers: `binds_weaken`, `okt_strengthen`, `map_subst_t_id` correspond to Coq `binds_weaken` (used inside proofs), strengthening (common env lemma), and `map_subst_id`.
- All other Lean theorems retain Coq names with minor list-based env notation changes (`&` ↔ `++`).
