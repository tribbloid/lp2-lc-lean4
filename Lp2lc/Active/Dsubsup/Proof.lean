import «Lp2lc».Active.Dsubsup.Def
import «Lp2lc».Active.Dsubsup.Auxiliary

namespace Lp2lc.Active.Dsubsup

open typ trm

-- Opening and substitution lemmas
/-- Coq: open_rec_lc_core -/ 
theorem open_rec_lc_core :
  (∀ T j v u i, i ≠ j →
    open_t_rec j v T = open_t_rec i u (open_t_rec j v T) →
    T = open_t_rec i u T) ∧
  (∀ e j v u i, i ≠ j →
    open_e_rec j v e = open_e_rec i u (open_e_rec j v e) →
    e = open_e_rec i u e) := by
  sorry

/-- Coq: open_rec_lc -/ 
theorem open_rec_lc :
  (∀ T, def_type T → ∀ u k, T = open_t_rec k u T) ∧
  (∀ e, def_term e → ∀ u k, e = open_e_rec k u e) := by
  sorry

/-- Coq: open_t_var_type -/ 
theorem open_t_var_type : ∀ x T,
  def_type T → T open_t_var x = T := by
  sorry

/-- Coq: subst_fresh -/ 
theorem subst_fresh :
  (∀ T z u, z ∉ fv_t T → subst_t z u T = T) ∧
  (∀ e z u, z ∉ fv_e e → subst_e z u e = e) := by
  sorry

/-- Coq: subst_open_rec -/ 
theorem subst_open_rec :
  (∀ T1 t2 x u n, def_term u →
    subst_t x u (open_t_rec n t2 T1) =
    open_t_rec n (subst_e x u t2) (subst_t x u T1)) ∧
  (∀ t1 t2 x u n, def_term u →
    subst_e x u (open_e_rec n t2 t1) =
    open_e_rec n (subst_e x u t2) (subst_e x u t1)) := by
  sorry

/-- Coq: subst_t_open_t -/ 
theorem subst_t_open_t : ∀ T1 t2 x u, def_term u →
  subst_t x u (open_t T1 t2) =
  open_t (subst_t x u T1) (subst_e x u t2) := by
  sorry

/-- Coq: subst_e_open_e -/ 
theorem subst_e_open_e : ∀ t1 t2 x u, def_term u →
  subst_e x u (open_e t1 t2) =
  open_e (subst_e x u t1) (subst_e x u t2) := by
  sorry

/-- Coq: subst_t_open_t_var -/ 
theorem subst_t_open_t_var : ∀ x y u T, y ≠ x → def_term u →
  (subst_t x u T) open_t_var y = subst_t x u (T open_t_var y) := by
  sorry

/-- Coq: subst_e_open_e_var -/ 
theorem subst_e_open_e_var : ∀ x y u e, y ≠ x → def_term u →
  (subst_e x u e) open_e_var y = subst_e x u (e open_e_var y) := by
  sorry

/-- Coq: subst_t_intro -/ 
theorem subst_t_intro : ∀ x T2 u,
  x ∉ fv_t T2 → def_term u →
  open_t T2 u = subst_t x u (T2 open_t_var x) := by
  sorry

/-- Coq: subst_e_intro -/ 
theorem subst_e_intro : ∀ x t2 u,
  x ∉ fv_e t2 → def_term u →
  open_e t2 u = subst_e x u (t2 open_e_var x) := by
  sorry

/-- Coq: subst_lc -/ 
theorem subst_lc :
  (∀ T, def_type T → ∀ z u, def_term u → def_type (subst_t z u T)) ∧
  (∀ e, def_term e → ∀ z u, def_term u → def_term (subst_e z u e)) := by
  sorry

/-- Coq: subst_t_type -/ 
theorem subst_t_type : ∀ T z u,
  def_type T → def_term u → def_type (subst_t z u T) := by
  sorry

/-- Coq: subst_e_term -/ 
theorem subst_e_term : ∀ e1 z e2,
  def_term e1 → def_term e2 → def_term (subst_e z e2 e1) := by
  sorry

/-- Coq: subst_e_value -/ 
theorem subst_e_value : ∀ e1 z e2,
  value e1 → def_term e2 → value (subst_e z e2 e1) := by
  sorry

/-- Coq: value_is_term -/ 
theorem value_is_term : ∀ e, value e → def_term e := by
  sorry

-- Wf properties and weakening/narrowing
/-- Coq: wf_lc -/ 
theorem wf_lc : (∀ E T, wft E T → def_type T) ∧ (∀ E e, wfe E e → def_term e) := by
  sorry

/-- Coq: wft_type -/ 
theorem wft_type : ∀ E T, wft E T → def_type T := by
  sorry

/-- Coq: wfe_term -/ 
theorem wfe_term : ∀ E e, wfe E e → def_term e := by
  sorry

/-- Coq: wf_weaken -/ 
theorem wf_weaken :
  (∀ E0 T, wft E0 T → ∀ E F G, E0 = E ++ G → ok (E ++ F ++ G) → wft (E ++ F ++ G) T) ∧
  (∀ E0 e, wfe E0 e → ∀ E F G, E0 = E ++ G → ok (E ++ F ++ G) → wfe (E ++ F ++ G) e) := by
  sorry

/-- Coq: wft_weaken -/ 
theorem wft_weaken : ∀ G T E F, wft (E ++ G) T → ok (E ++ F ++ G) → wft (E ++ F ++ G) T := by
  sorry

/-- Coq: wfe_weaken -/ 
theorem wfe_weaken : ∀ G T E F, wfe (E ++ G) T → ok (E ++ F ++ G) → wfe (E ++ F ++ G) T := by
  sorry

/-- Coq: wf_narrow -/ 
theorem wf_narrow :
  (∀ E0 T, wft E0 T → ∀ V F U E x, E0 = (E ++ (x, V) :: F) → ok (E ++ (x, U) :: F) → wft (E ++ (x, U) :: F) T) ∧
  (∀ E0 e, wfe E0 e → ∀ V F U E x, E0 = (E ++ (x, V) :: F) → ok (E ++ (x, U) :: F) → wfe (E ++ (x, U) :: F) e) := by
  sorry

/-- Coq: wft_narrow -/ 
theorem wft_narrow : ∀ V F U T E x, wft (E ++ (x, V) :: F) T → ok (E ++ (x, U) :: F) → wft (E ++ (x, U) :: F) T := by
  sorry

-- Substitution through env
/-- Coq: wf_subst -/ 
theorem wf_subst :
  (∀ E0 T, wft E0 T → ∀ F Q E Z u,
    E0 = E ++ (Z, Q) :: F → (value u ∨ ∃ x, trm_fvar x = u) → wfe E u → ok (E ++ (map (fun p => (p.1, subst_t Z u p.2)) F)) →
    wft (E ++ (map (fun p => (p.1, subst_t Z u p.2)) F)) (subst_t Z u T)) ∧
  (∀ E0 e, wfe E0 e → ∀ F Q E Z u,
    E0 = E ++ (Z, Q) :: F → (value u ∨ ∃ x, trm_fvar x = u) → wfe E u → ok (E ++ (map (fun p => (p.1, subst_t Z u p.2)) F)) →
    wfe (E ++ (map (fun p => (p.1, subst_t Z u p.2)) F)) (subst_e Z u e)) := by
  sorry

/-- Coq: wft_subst -/ 
theorem wft_subst : ∀ F Q E Z u T,
  wft (E ++ (Z, Q) :: F) T → (value u ∨ ∃ x, trm_fvar x = u) → wfe E u → ok (E ++ (map (fun p => (p.1, subst_t Z u p.2)) F)) →
  wft (E ++ (map (fun p => (p.1, subst_t Z u p.2)) F)) (subst_t Z u T) := by
  sorry

/-- Coq: wft_subst1 -/ 
theorem wft_subst1 : ∀ F Q Z u T,
  wft ((Z, Q) :: F) T → (value u ∨ ∃ x, trm_fvar x = u) → wfe [] u → ok (map (fun p => (p.1, subst_t Z u p.2)) F) →
  wft (map (fun p => (p.1, subst_t Z u p.2)) F) (subst_t Z u T) := by
  sorry

/-- Coq: wft_subst_empty -/ 
theorem wft_subst_empty : ∀ Q Z u T,
  wft [(Z, Q)] T → (value u ∨ ∃ x, trm_fvar x = u) → wfe [] u → wft [] (subst_t Z u T) := by
  sorry

/-- Coq: wft_open -/ 
theorem wft_open : ∀ E u T1 T2,
  ok E → wft E (typ_all T1 T2) → (value u ∨ ∃ x, trm_fvar x = u) → wfe E u → wft E (open_t T2 u) := by
  sorry

-- Env relations and regularity
/-- Coq: ok_from_okt -/ 
theorem ok_from_okt : ∀ E, okt E → ok E := by
  sorry

/-- Coq: wft_from_env_has -/ 
theorem wft_from_env_has : ∀ x U E, okt E → binds x U E → wft E U := by
  sorry

/-- Coq: wft_from_okt -/ 
theorem wft_from_okt : ∀ x T E, okt ((x, T) :: E) → wft E T := by
  sorry

/-- Coq: wft_weaken_right -/ 
theorem wft_weaken_right : ∀ T E F, wft E T → ok (E ++ F) → wft (E ++ F) T := by
  sorry

/-- Coq: sub_has_regular -/ 
theorem sub_has_regular :
  (∀ E S T, sub E S T → okt E ∧ wft E S ∧ wft E T) ∧
  (∀ E p T, has E p T → okt E ∧ wft E (typ_sel p) ∧ wft E T) := by
  sorry

-- Weakening/narrowing for sub/has
/-- Coq: sub_has_weakening -/ 
theorem sub_has_weakening :
  (∀ E0 S T, sub E0 S T → ∀ E F G, E0 = E ++ G → okt (E ++ F ++ G) → sub (E ++ F ++ G) S T) ∧
  (∀ E0 p T, has E0 p T → ∀ E F G, E0 = E ++ G → okt (E ++ F ++ G) → has (E ++ F ++ G) p T) := by
  sorry

/-- Coq: sub_weakening -/ 
theorem sub_weakening : ∀ E F G S T, sub (E ++ G) S T → okt (E ++ F ++ G) → sub (E ++ F ++ G) S T := by
  sorry

/-- Coq: has_weakening -/ 
theorem has_weakening : ∀ E F G p T, has (E ++ G) p T → okt (E ++ F ++ G) → has (E ++ F ++ G) p T := by
  sorry

/-- Coq: sub_has_narrowing_aux -/ 
theorem sub_has_narrowing_aux :
  (∀ E0 S T, sub E0 S T → ∀ Q E F z P, E0 = (E ++ (z, Q) :: F) → sub E P Q → sub (E ++ (z, P) :: F) S T) ∧
  (∀ E0 p T, has E0 p T → ∀ Q E F z P, E0 = (E ++ (z, Q) :: F) → sub E P Q → has (E ++ (z, P) :: F) p T) := by
  sorry

/-- Coq: sub_narrowing -/ 
theorem sub_narrowing : ∀ Q E F Z P S T, sub E P Q → sub (E ++ (Z, Q) :: F) S T → sub (E ++ (Z, P) :: F) S T := by
  sorry

-- Substitution preserves subtyping
/-- Coq: has_value_var -/ 
theorem has_value_var : ∀ E u T, has E u T → (value u ∨ ∃ x, trm_fvar x = u) := by
  sorry

/-- Coq: var_typing_has -/ 
theorem var_typing_has : ∀ E x Q, typing E (trm_fvar x) Q → has E (trm_fvar x) Q := by
  sorry

/-- Coq: val_typing_has -/ 
theorem val_typing_has : ∀ E u Q, value u → typing E u Q → has E u Q := by
  sorry

/-- Coq: sub_has_through_subst -/ 
theorem sub_has_through_subst :
  (∀ E0 S T, sub E0 S T → ∀ Q E F Z u, E0 = (E ++ (Z, Q) :: F) → (value u ∨ ∃ x, trm_fvar x = u) → typing E u Q →
     sub (E ++ (map (fun p => (p.1, subst_t Z u p.2)) F)) (subst_t Z u S) (subst_t Z u T)) ∧
  (∀ E0 p T, has E0 p T → ∀ Q E F Z u, E0 = (E ++ (Z, Q) :: F) → (value u ∨ ∃ x, trm_fvar x = u) → typing E u Q →
     has (E ++ (map (fun p => (p.1, subst_t Z u p.2)) F)) (subst_e Z u p) (subst_t Z u T)) := by
  sorry

-- Typing properties
/-- Coq: typing_weakening -/ 
theorem typing_weakening : ∀ E F G e T, typing (E ++ G) e T → okt (E ++ F ++ G) → typing (E ++ F ++ G) e T := by
  sorry

/-- Coq: typing_narrowing -/ 
theorem typing_narrowing : ∀ Q E F X P e T, sub E P Q → typing (E ++ (X, Q) :: F) e T → typing (E ++ (X, P) :: F) e T := by
  sorry

/-- Coq: typing_through_subst -/ 
theorem typing_through_subst : ∀ U E F z T e u, typing (E ++ (z, U) :: F) e T → (value u ∨ ∃ x, trm_fvar x = u) → typing E u U →
  typing (E ++ (map (fun p => (p.1, subst_t z u p.2)) F)) (subst_e z u e) (subst_t z u T) := by
  sorry

/-- Coq: typing_through_subst1 -/ 
theorem typing_through_subst1 : ∀ V y v e T, typing [(y, V)] e T → value v → typing [] v V → typing [] (subst_e y v e) (subst_t y v T) := by
  sorry

-- Canonical forms / results
/-- Coq: has_empty_value -/ 
theorem has_empty_value : ∀ p T, has [] p T → value p := by
  sorry

/-- Coq: typing_inv_abs (via possible types) -/ 
/-- Skipped detailed possible_types framework; keep statement scaffold. -/

/-- Coq: canonical_form_abs -/ 
theorem canonical_form_abs : ∀ t U1 U2, value t → typing [] t (typ_all U1 U2) → ∃ V e1, t = trm_abs V e1 := by
  sorry

/-- Coq: canonical_form_mem -/ 
theorem canonical_form_mem : ∀ t b T, value t → typing [] t (typ_mem b T) → ∃ V, t = trm_mem V := by
  sorry

/-- Coq: preservation_result -/ 
theorem preservation_result : preservation := by
  simp [preservation]
  sorry

/-- Coq: progress_result -/ 
theorem progress_result : progress := by
  simp [progress]
  sorry

end Lp2lc.Active.Dsubsup
