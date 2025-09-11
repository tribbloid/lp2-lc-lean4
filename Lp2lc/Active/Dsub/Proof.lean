import «Lp2lc».Active.Dsub.Def
import «Lp2lc».Active.Dsub.Auxiliary

namespace Lp2lc.Active.Dsub

open typ trm

-- Opening and substitution lemmas (scaffolding)
/-- Coq: open_rec_lc_core -/ 
@[simp] theorem open_rec_lc_core :
  (∀ T j v u i, i ≠ j →
    open_t_rec j v T = open_t_rec i u (open_t_rec j v T) →
    T = open_t_rec i u T) ∧
  (∀ e j v u i, i ≠ j →
    open_e_rec j v e = open_e_rec i u (open_e_rec j v e) →
    e = open_e_rec i u e) := by
  sorry

/-- Coq: open_rec_lc -/ 
@[simp] theorem open_rec_lc :
  (∀ T, def_type T → ∀ u k, T = open_t_rec k u T) ∧
  (∀ e, def_term e → ∀ u k, e = open_e_rec k u e) := by
  sorry

/-- Coq: open_t_var_type -/ 
@[simp] theorem open_t_var_type : ∀ (x : Var) (T : typ),
  def_type T → open_t T (trm_fvar x) = T := by
  sorry

/-- Coq: subst_fresh -/ 
@[simp] theorem subst_fresh :
  (∀ T z u, z ∉ fv_t T → subst_t z u T = T) ∧
  (∀ e z u, z ∉ fv_e e → subst_e z u e = e) := by
  sorry

/-- Coq: subst_open_rec -/ 
@[simp] theorem subst_open_rec :
  (∀ T1 t2 x u n, def_term u →
    subst_t x u (open_t_rec n t2 T1) =
    open_t_rec n (subst_e x u t2) (subst_t x u T1)) ∧
  (∀ t1 t2 x u n, def_term u →
    subst_e x u (open_e_rec n t2 t1) =
    open_e_rec n (subst_e x u t2) (subst_e x u t1)) := by
  sorry

/-- Coq: subst_t_open_t -/ 
@[simp] theorem subst_t_open_t : ∀ T1 t2 x u, def_term u →
  subst_t x u (open_t T1 t2) =
  open_t (subst_t x u T1) (subst_e x u t2) := by
  sorry

/-- Coq: subst_e_open_e -/ 
@[simp] theorem subst_e_open_e : ∀ t1 t2 x u, def_term u →
  subst_e x u (open_e t1 t2) =
  open_e (subst_e x u t1) (subst_e x u t2) := by
  sorry

-- Regularity and automation (scaffold)
/-- Coq: sub_has_regular -/ 
@[simp] theorem sub_has_regular :
  (∀ E S T, sub E S T → okt E ∧ wft E S ∧ wft E T) ∧
  (∀ E p T, has E p T → okt E ∧ wft E (typ_sel p) ∧ wft E T) := by
  sorry

@[simp] theorem sub_regular : ∀ E S T, sub E S T → okt E ∧ wft E S ∧ wft E T := by
  sorry

@[simp] theorem has_regular : ∀ E p T, has E p T → okt E ∧ wft E (typ_sel p) ∧ wft E T := by
  sorry

@[simp] theorem has_regular_e : ∀ E p T, has E p T → (value p ∨ ∃ x, trm_fvar x = p) ∧ wfe E p := by
  sorry

/-- Coq: typing_regular -/ 
@[simp] theorem typing_regular : ∀ E e T, typing E e T → okt E ∧ wfe E e ∧ wft E T := by
  sorry

@[simp] theorem value_regular : ∀ t, value t → def_term t := by
  sorry

@[simp] theorem red_regular : ∀ t t', red t t' → def_term t ∧ def_term t' := by
  sorry

-- Subtyping properties
/-- Coq: sub_reflexivity -/ 
@[simp] theorem sub_reflexivity : ∀ E T, okt E → wft E T → sub E T T := by
  sorry

/-- Coq: sub_has_weakening and corollaries -/ 
@[simp] theorem sub_has_weakening :
  (∀ E0 S T, sub E0 S T → ∀ E F G, E0 = E ++ G → ok (E ++ F ++ G) → sub (E ++ F ++ G) S T) ∧
  (∀ E0 p T, has E0 p T → ∀ E F G, E0 = E ++ G → ok (E ++ F ++ G) → has (E ++ F ++ G) p T) := by
  sorry

@[simp] theorem sub_weakening : ∀ E F G S T, sub (E ++ G) S T → ok (E ++ F ++ G) → sub (E ++ F ++ G) S T := by
  sorry

@[simp] theorem sub_weakening1 : ∀ E F G S T, sub E S T → ok (E ++ F ++ G) → sub (E ++ F ++ G) S T := by
  sorry

@[simp] theorem sub_weakening_empty : ∀ E S T, sub [] S T → ok E → sub E S T := by
  sorry

@[simp] theorem has_weakening : ∀ E F G p T, has (E ++ G) p T → ok (E ++ F ++ G) → has (E ++ F ++ G) p T := by
  sorry

@[simp] theorem has_weakening1 : ∀ E F G p T, has E p T → ok (E ++ F ++ G) → has (E ++ F ++ G) p T := by
  sorry

@[simp] theorem has_weakening_empty : ∀ E p T, has [] p T → ok E → has E p T := by
  sorry

-- Narrowing
@[simp] theorem sub_has_narrowing_aux :
  (∀ E0 S T, sub E0 S T → ∀ Q E F z P, E0 = (E ++ (z, Q) :: F) → sub E P Q → sub (E ++ (z, P) :: F) S T) ∧
  (∀ E0 p T, has E0 p T → ∀ Q E F z P, E0 = (E ++ (z, Q) :: F) → sub E P Q → has (E ++ (z, P) :: F) p T) := by
  sorry

@[simp] theorem sub_narrowing : ∀ Q E F Z P S T, sub E P Q → sub (E ++ (Z, Q) :: F) S T → sub (E ++ (Z, P) :: F) S T := by
  sorry

@[simp] theorem sub_narrowing_empty : ∀ Q Z P S T, sub [] P Q → sub [(Z, Q)] S T → sub [(Z, P)] S T := by
  sorry

-- Substitution preserves sub/has
@[simp] theorem has_value_var : ∀ E u T, has E u T → (value u ∨ ∃ x, trm_fvar x = u) := by
  sorry

@[simp] theorem var_typing_has : ∀ E x Q, typing E (trm_fvar x) Q → has E (trm_fvar x) Q := by
  sorry

@[simp] theorem val_typing_has : ∀ E u Q, value u → typing E u Q → has E u Q := by
  sorry

@[simp] theorem sub_has_through_subst :
  (∀ E0 S T, sub E0 S T → ∀ Q E F Z u,
    E0 = (E ++ (Z, Q) :: F) → (value u ∨ ∃ x, trm_fvar x = u) → typing E u Q →
    sub (E ++ (List.map (fun p => (p.1, subst_t Z u p.2)) F)) (subst_t Z u S) (subst_t Z u T)) ∧
  (∀ E0 p T, has E0 p T → ∀ Q E F Z u,
    E0 = (E ++ (Z, Q) :: F) → (value u ∨ ∃ x, trm_fvar x = u) → typing E u Q →
    has (E ++ (List.map (fun p => (p.1, subst_t Z u p.2)) F)) (subst_e Z u p) (subst_t Z u T)) := by
  sorry

-- Typing properties
@[simp] theorem typing_weakening : ∀ E F G e T, typing (E ++ G) e T → ok (E ++ F ++ G) → typing (E ++ F ++ G) e T := by
  sorry

@[simp] theorem typing_narrowing : ∀ Q E F X P e T, sub E P Q → typing (E ++ (X, Q) :: F) e T → typing (E ++ (X, P) :: F) e T := by
  sorry

@[simp] theorem typing_narrowing_empty : ∀ Q X P e T, sub [] P Q → typing [(X, Q)] e T → typing [(X, P)] e T := by
  sorry

@[simp] theorem typing_through_subst : ∀ U E F z T e u,
  typing (E ++ (z, U) :: F) e T → (value u ∨ ∃ x, trm_fvar x = u) → typing E u U →
  typing (E ++ List.map (fun p => (p.1, subst_t z u p.2)) F) (subst_e z u e) (subst_t z u T) := by
  sorry

-- Inversions and canonical forms
@[simp] theorem psub_sub : ∀ S T, psub S T → sub [] S T := by
  sorry

@[simp] theorem possible_types_value : ∀ n p T, possible_types n p T → value p := by
  sorry

@[simp] theorem possible_types_wfe : ∀ n p T, possible_types n p T → wfe [] p := by
  sorry

@[simp] theorem possible_types_wft : ∀ n p T, possible_types n p T → wft [] T := by
  sorry

@[simp] theorem has_empty_value : ∀ p T, has [] p T → value p := by
  sorry

@[simp] theorem has_empty_var_false : ∀ x T, has [] (trm_fvar x) T → False := by
  sorry

@[simp] theorem possible_types_closure_psub : ∀ n v T U, possible_types n v T → psub T U → possible_types n v U := by
  sorry

@[simp] theorem psub_reflexivity : ∀ T, wft [] T → psub T T := by
  sorry

@[simp] theorem sub_psub : ∀ S T, sub [] S T → psub S T := by
  sorry

@[simp] theorem possible_types_closure : ∀ n v T U, possible_types n v T → sub [] T U → possible_types n v U := by
  sorry

@[simp] theorem possible_types_typing : ∀ v T, typing [] v T → value v → possible_types 1 v T := by
  sorry

@[simp] theorem typing_inv_abs : ∀ (S1 : typ) (e1 : trm) (T : typ),
  typing [] (trm_abs S1 e1) T → ∀ (U1 U2 : typ), sub [] T (typ_all U1 U2) →
  sub [] U1 S1 ∧ ∃ (S2 : typ) (L : Vars), ∀ (x : Var), x ∉ L →
    typing [(x, S1)] (open_e e1 (trm_fvar x)) (open_t S2 (trm_fvar x)) ∧
    sub [(x, U1)] (open_t S2 (trm_fvar x)) (open_t U2 (trm_fvar x)) := by
  sorry

@[simp] theorem canonical_form_abs : ∀ t U1 U2, value t → typing [] t (typ_all U1 U2) → ∃ V, ∃ e1, t = trm_abs V e1 := by
  sorry

@[simp] theorem canonical_form_mem : ∀ t b T, value t → typing [] t (typ_mem b T) → ∃ V, t = trm_mem V := by
  sorry

@[simp] theorem typing_through_subst1 : ∀ V y v e T, typing [(y, V)] e T → value v → typing [] v V → typing [] (subst_e y v e) (subst_t y v T) := by
  sorry

-- Preservation and progress
@[simp] theorem value_red_contra : ∀ e e', value e → red e e' → False := by
  sorry

@[simp] theorem preservation_result : preservation := by
  sorry

@[simp] theorem progress_result : progress := by
  sorry

end Lp2lc.Active.Dsub
