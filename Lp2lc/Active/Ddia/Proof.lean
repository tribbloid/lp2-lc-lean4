/-****************************************************************************
* Ddia (DOT-style calculus) – Theorems (scaffold)
* All proofs are `sorry` placeholders per 1_Scaffold.md; no axioms introduced.
*****************************************************************************-/

import Aesop
import «Lp2lc».Active.Ddia.Def
import «Lp2lc».Active.Ddia.Auxiliary

namespace Lp2lc.Active.Ddia

open typ trm def_type def_term wft wfe value sub has typing red

/- Selection of core lemmas stubbed to establish structure. The full list
   is tracked in Proof.progress.md and will be added incrementally. -/

-- Coq line 596: Lemma value_is_term
theorem value_is_term : ∀ e, value e → def_term e := by
  intro e h; cases h <;> aesop

-- Coq line 614: Lemma wft_type
theorem wft_type : ∀ {E T}, wft E T → def_type T := by
  -- TODO: will be proved using mutual recursion with wfe_term and regularity lemmas
  intro _ _ _; sorry

-- Coq line 1116: Lemma sub_reflexivity
theorem sub_reflexivity : ∀ {E T}, okt E → wft E T → sub E T T := by
  intro E T hOk hW; 
  -- TODO: structural induction over hW, cofinite in all-case
  sorry

-- Coq line 1024: Lemma typing_regular
theorem typing_regular : ∀ {E e T}, typing E e T → okt E ∧ wfe E e ∧ wft E T := by
  -- TODO: structural cases on typing
  sorry

-- Coq line 1821: Preservation result
theorem preservation_result : preservation := by
  -- TODO: standard preservation using inversion and substitution lemmas
  sorry

-- Coq line 1864: Progress result
theorem progress_result : progress := by
  -- TODO: standard progress via canonical forms and inversion
  sorry

-- A few substitution lemmas (stubs)
-- Coq line 574: Lemma subst_e_term
theorem subst_e_term : ∀ {e1 z e2}, def_term e1 → def_term e2 → def_term (subst_e z e2 e1) := by
  -- TODO: mutual induction over terms
  sorry

-- Coq line 568: Lemma subst_t_type (adapted to Ddia: subst over types uses terms)
theorem subst_t_type : ∀ {T z u}, def_type T → def_term u → def_type (subst_t z u T) := by
  -- TODO: mutual induction over types/terms
  sorry

-- Additional scaffolds listed in Proof.progress.md (placeholders)
-- Opening / substitution infrastructure
@[simp] theorem open_rec_lc_core_true : True := by
  -- placeholder for: open_rec_lc_core
  sorry
@[simp] theorem open_rec_lc_true : True := by
  -- placeholder for: open_rec_lc
  sorry
@[simp] theorem open_t_var_type_true : True := by
  -- placeholder for: open_t_var_type
  sorry
@[simp] theorem subst_fresh_true : True := by
  -- placeholder for: subst_fresh
  sorry
@[simp] theorem subst_open_rec_true : True := by
  -- placeholder for: subst_open_rec
  sorry
@[simp] theorem subst_t_open_t_true : True := by
  -- placeholder for: subst_t_open_t
  sorry
@[simp] theorem subst_e_open_e_true : True := by
  -- placeholder for: subst_e_open_e
  sorry
@[simp] theorem subst_t_open_t_var_true : True := by
  -- placeholder for: subst_t_open_t_var
  sorry
@[simp] theorem subst_e_open_e_var_true : True := by
  -- placeholder for: subst_e_open_e_var
  sorry
@[simp] theorem subst_t_intro_true : True := by
  -- placeholder for: subst_t_intro
  sorry
@[simp] theorem subst_e_intro_true : True := by
  -- placeholder for: subst_e_intro
  sorry
@[simp] theorem subst_lc_true : True := by
  -- placeholder for: subst_lc
  sorry

-- Regularity scaffolds and helpers
@[simp] theorem wf_lc_true : True := by sorry
@[simp] theorem wfe_term_true : True := by sorry

-- Weakening / narrowing / substitution for wf/wfe
@[simp] theorem wf_weaken_true : True := by sorry
@[simp] theorem wft_weaken_true : True := by sorry
@[simp] theorem wft_weaken_empty_true : True := by sorry
@[simp] theorem wfe_weaken_true : True := by sorry
@[simp] theorem wfe_weaken_empty_true : True := by sorry
@[simp] theorem wf_narrow_true : True := by sorry
@[simp] theorem wft_narrow_true : True := by sorry
@[simp] theorem wf_subst_true : True := by sorry
@[simp] theorem wft_subst_true : True := by sorry
@[simp] theorem wft_subst1_true : True := by sorry
@[simp] theorem wft_subst_empty_true : True := by sorry
@[simp] theorem wft_open_true : True := by sorry

-- Environment properties
@[simp] theorem ok_from_okt_true : True := by sorry
@[simp] theorem wft_from_env_has_true : True := by sorry
@[simp] theorem wft_from_okt_true : True := by sorry
@[simp] theorem wft_weaken_right_true : True := by sorry
@[simp] theorem okt_push_inv_true : True := by sorry
@[simp] theorem okt_push_type_true : True := by sorry
@[simp] theorem okt_narrow_true : True := by sorry
@[simp] theorem okt_subst_true : True := by sorry
@[simp] theorem okt_subst1_true : True := by sorry

-- Free variable properties
@[simp] theorem notin_fv_open_rec_true : True := by sorry
@[simp] theorem notin_fv_t_open_true : True := by sorry
@[simp] theorem notin_fv_e_open_true : True := by sorry
@[simp] theorem notin_fv_wf_rec_true : True := by sorry
@[simp] theorem notin_fv_wf_true : True := by sorry
@[simp] theorem map_subst_id_true : True := by sorry

-- Regularity of relations
@[simp] theorem sub_has_regular_true : True := by sorry
@[simp] theorem sub_regular_true : True := by sorry
@[simp] theorem has_regular_true : True := by sorry
@[simp] theorem has_regular_e_true : True := by sorry

-- Subtyping: weakening, narrowing, substitution
@[simp] theorem sub_has_weakening_true : True := by sorry
@[simp] theorem sub_weakening_true : True := by sorry
@[simp] theorem sub_weakening1_true : True := by sorry
@[simp] theorem sub_weakening_empty_true : True := by sorry
@[simp] theorem has_weakening_true : True := by sorry
@[simp] theorem has_weakening1_true : True := by sorry
@[simp] theorem has_weakening_empty_true : True := by sorry
@[simp] theorem sub_has_narrowing_aux_true : True := by sorry
@[simp] theorem sub_narrowing_true : True := by sorry
@[simp] theorem sub_narrowing_empty_true : True := by sorry

-- Has/Typing bridges and substitution-through-subtyping
@[simp] theorem has_value_var_true : True := by sorry
@[simp] theorem var_typing_has_true : True := by sorry
@[simp] theorem val_typing_has_true : True := by sorry
@[simp] theorem sub_has_through_subst_true : True := by sorry

-- Typing weakening/narrowing/substitution
@[simp] theorem typing_weakening_true : True := by sorry
@[simp] theorem typing_narrowing_true : True := by sorry
@[simp] theorem typing_narrowing_empty_true : True := by sorry
@[simp] theorem typing_through_subst_true : True := by sorry

-- Pseudo-subtyping and canonical forms
@[simp] theorem psub_sub_true : True := by sorry
@[simp] theorem possible_types_value_true : True := by sorry
@[simp] theorem possible_types_wfe_true : True := by sorry
@[simp] theorem possible_types_wft_true : True := by sorry
@[simp] theorem has_empty_var_false_true : True := by sorry
@[simp] theorem possible_types_closure_psub_true : True := by sorry
@[simp] theorem psub_reflexivity_true : True := by sorry
@[simp] theorem sub_psub_aux_true : True := by sorry
@[simp] theorem sub_psub_true : True := by sorry
@[simp] theorem possible_types_closure_true : True := by sorry
@[simp] theorem possible_types_typing_true : True := by sorry
@[simp] theorem typing_inv_abs_true : True := by sorry
@[simp] theorem canonical_form_abs_true : True := by sorry
@[simp] theorem canonical_form_mem_true : True := by sorry
@[simp] theorem typing_through_subst1_true : True := by sorry
@[simp] theorem value_red_contra_true : True := by sorry

end Lp2lc.Active.Ddia
