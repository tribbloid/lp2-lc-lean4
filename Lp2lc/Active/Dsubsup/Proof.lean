import «Lp2lc».Active.Dsubsup.Def
import «Lp2lc».Active.Dsubsup.Auxiliary

namespace Lp2lc.Active.Dsubsup

open typ trm

-- Coq lemma index (91 items) TODO scaffold in order with [Coq L###]
/-
See: gen/plan/Define/Dsubsup.coq.index
We will add theorem stubs in the same order, each annotated with its Coq line, and
gradually refine signatures and proofs. This preserves build stability.
-/

-- Minimal early lemmas scaffolding (fill later)
@[simp] theorem open_rec_lc_core :
  (∀ T j v u i, i ≠ j → open_t_rec j v T = open_t_rec i u (open_t_rec j v T) → T = open_t_rec i u T) ∧
  (∀ e j v u i, i ≠ j → open_e_rec j v e = open_e_rec i u (open_e_rec j v e) → e = open_e_rec i u e) := by
  sorry

@[simp] theorem open_rec_lc :
  (∀ T, def_type T → ∀ u k, T = open_t_rec k u T) ∧ (∀ e, def_term e → ∀ u k, e = open_e_rec k u e) := by
  sorry

axiom open_t_var_type : Prop

@[simp] theorem subst_fresh :
  (∀ T z u, z ∉ fv_t T → subst_t z u T = T) ∧ (∀ e z u, z ∉ fv_e e → subst_e z u e = e) := by
  sorry

-- Placeholders to synchronize with Proof.progress.md (to be replaced with real statements)
axiom subst_open_rec : Prop
axiom subst_t_open_t : Prop
axiom subst_e_open_e : Prop
axiom subst_t_open_t_var : Prop
axiom subst_e_open_e_var : Prop
axiom subst_t_intro : Prop
axiom subst_e_intro : Prop
axiom subst_lc : Prop
axiom subst_t_type : Prop
axiom subst_e_term : Prop
axiom subst_e_value : Prop
axiom value_is_term : Prop
axiom wf_lc : Prop
axiom wft_type : Prop
axiom wfe_term : Prop
axiom wf_weaken : Prop
axiom wft_weaken : Prop
axiom wft_weaken_empty : Prop
axiom wfe_weaken : Prop
axiom wfe_weaken_empty : Prop
axiom wf_narrow : Prop
axiom wft_narrow : Prop
axiom wf_subst : Prop
axiom wft_subst : Prop
axiom wft_subst1 : Prop
axiom wft_subst_empty : Prop
axiom wft_open : Prop
axiom ok_from_okt : Prop
axiom wft_from_env_has : Prop
axiom wft_from_okt : Prop
axiom wft_weaken_right : Prop
axiom okt_push_inv : Prop
axiom okt_push_type : Prop
axiom okt_narrow : Prop
axiom okt_subst : Prop
axiom okt_subst1 : Prop
axiom notin_fv_open_rec : Prop
axiom notin_fv_t_open : Prop
axiom notin_fv_e_open : Prop
axiom notin_fv_wf_rec : Prop
axiom notin_fv_wf : Prop
axiom map_subst_id : Prop
axiom sub_has_regular : Prop
axiom sub_regular : Prop
axiom has_regular : Prop
axiom has_regular_e : Prop
axiom typing_regular : Prop
axiom value_regular : Prop
axiom red_regular : Prop
axiom sub_reflexivity : Prop
axiom sub_has_weakening : Prop
axiom sub_weakening : Prop
axiom sub_weakening1 : Prop
axiom sub_weakening_empty : Prop
axiom has_weakening : Prop
axiom has_weakening1 : Prop
axiom has_weakening_empty : Prop
axiom sub_has_narrowing_aux : Prop
axiom sub_narrowing : Prop
axiom sub_narrowing_empty : Prop
axiom has_value_var : Prop
axiom var_typing_has : Prop
axiom val_typing_has : Prop
axiom sub_has_through_subst : Prop
axiom typing_weakening : Prop
axiom typing_narrowing : Prop
axiom typing_narrowing_empty : Prop
axiom typing_through_subst : Prop
axiom has_empty_value : Prop
axiom psub_sub : Prop
axiom possible_types_value : Prop
axiom possible_types_wfe : Prop
axiom possible_types_wft : Prop
axiom has_empty_var_false : Prop
axiom possible_types_closure_psub : Prop
axiom psub_reflexivity : Prop
axiom sub_psub_aux : Prop
axiom sub_psub : Prop
axiom possible_types_closure : Prop
axiom possible_types_typing : Prop
axiom typing_inv_abs : Prop
axiom canonical_form_abs : Prop
axiom canonical_form_mem : Prop
axiom typing_through_subst1 : Prop
axiom value_red_contra : Prop
axiom preservation_result : Prop
axiom progress_result : Prop

end Lp2lc.Active.Dsubsup
