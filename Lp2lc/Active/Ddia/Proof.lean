import «Lp2lc».Active.Ddia.Def
import «Lp2lc».Active.Ddia.Auxiliary

namespace Lp2lc.Active.Ddia

open typ trm

-- Opening and substitution lemmas
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

/-- Coq: subst_t_open_t_var -/ 
@[simp] theorem subst_t_open_t_var : ∀ (x y : Var) (u : trm) (T : typ), y ≠ x → def_term u →
  open_t (subst_t x u T) (trm_fvar y) = subst_t x u (open_t T (trm_fvar y)) := by
  sorry

/-- Coq: subst_e_open_e_var -/ 
@[simp] theorem subst_e_open_e_var : ∀ (x y : Var) (u e : trm), y ≠ x → def_term u →
  open_e (subst_e x u e) (trm_fvar y) = subst_e x u (open_e e (trm_fvar y)) := by
  sorry

/-- Coq: subst_t_intro -/ 
@[simp] theorem subst_t_intro : ∀ (x : Var) (T2 : typ) (u : trm),
  x ∉ fv_t T2 → def_term u →
  open_t T2 u = subst_t x u (open_t T2 (trm_fvar x)) := by
  sorry

/-- Coq: subst_e_intro -/ 
@[simp] theorem subst_e_intro : ∀ (x : Var) (t2 u : trm),
  x ∉ fv_e t2 → def_term u →
  open_e t2 u = subst_e x u (open_e t2 (trm_fvar x)) := by
  sorry

/-- Coq: subst_lc -/ 
@[simp] theorem subst_lc :
  (∀ T, def_type T → ∀ z u, def_term u → def_type (subst_t z u T)) ∧
  (∀ e, def_term e → ∀ z u, def_term u → def_term (subst_e z u e)) := by
  sorry

/-- Coq: subst_t_type -/ 
@[simp] theorem subst_t_type : ∀ T z u,
  def_type T → def_term u → def_type (subst_t z u T) := by
  sorry

/-- Coq: subst_e_term -/ 
@[simp] theorem subst_e_term : ∀ e1 z e2,
  def_term e1 → def_term e2 → def_term (subst_e z e2 e1) := by
  sorry

/-- Coq: subst_e_value -/ 
@[simp] theorem subst_e_value : ∀ e1 z e2,
  value e1 → def_term e2 → value (subst_e z e2 e1) := by
  sorry

/-- Coq: value_is_term -/ 
@[simp] theorem value_is_term : ∀ e, value e → def_term e := by
  sorry

-- Wf properties and weakening/narrowing
/-- Coq: wf_lc -/ 
@[simp] theorem wf_lc : (∀ E T, wft E T → def_type T) ∧ (∀ E e, wfe E e → def_term e) := by
  sorry

/-- Coq: wft_type -/ 
@[simp] theorem wft_type : ∀ E T, wft E T → def_type T := by
  sorry

/-- Coq: wfe_term -/ 
@[simp] theorem wfe_term : ∀ E e, wfe E e → def_term e := by
  sorry

/-- Coq: wf_weaken -/ 
@[simp] theorem wf_weaken :
  (∀ E0 T, wft E0 T → ∀ E F G, E0 = E ++ G → ok (E ++ F ++ G) → wft (E ++ F ++ G) T) ∧
  (∀ E0 e, wfe E0 e → ∀ E F G, E0 = E ++ G → ok (E ++ F ++ G) → wfe (E ++ F ++ G) e) := by
  sorry

/-- Coq: wft_weaken -/ 
@[simp] theorem wft_weaken : ∀ G T E F, wft (E ++ G) T → ok (E ++ F ++ G) → wft (E ++ F ++ G) T := by
  sorry

@[simp] theorem wft_weaken_empty : ∀ T E, wft [] T → ok E → wft E T := by
  sorry

@[simp] theorem wfe_weaken : ∀ G T E F, wfe (E ++ G) T → ok (E ++ F ++ G) → wfe (E ++ F ++ G) T := by
  sorry

@[simp] theorem wfe_weaken_empty : ∀ t E, wfe [] t → ok E → wfe E t := by
  sorry

/-- Coq: wf_narrow -/ 
@[simp] theorem wf_narrow :
  (∀ E0 T, wft E0 T → ∀ V F U E x, E0 = (E ++ (x, V) :: F) → ok (E ++ (x, U) :: F) → wft (E ++ (x, U) :: F) T) ∧
  (∀ E0 e, wfe E0 e → ∀ V F U E x, E0 = (E ++ (x, V) :: F) → ok (E ++ (x, U) :: F) → wfe (E ++ (x, U) :: F) e) := by
  sorry

/-- Coq: wft_narrow -/ 
@[simp] theorem wft_narrow : ∀ V F U T E x, wft (E ++ (x, V) :: F) T → ok (E ++ (x, U) :: F) → wft (E ++ (x, U) :: F) T := by
  sorry

-- Substitution through env
/-- Coq: wf_subst -/ 
@[simp] theorem wf_subst :
  (∀ E0 T, wft E0 T → ∀ F Q E Z u,
    E0 = E ++ (Z, Q) :: F → (value u ∨ ∃ x, trm_fvar x = u) → wfe E u → ok (E ++ (List.map (fun p => (p.1, subst_t Z u p.2)) F)) →
    wft (E ++ (List.map (fun p => (p.1, subst_t Z u p.2)) F)) (subst_t Z u T)) ∧
  (∀ E0 e, wfe E0 e → ∀ F Q E Z u,
    E0 = E ++ (Z, Q) :: F → (value u ∨ ∃ x, trm_fvar x = u) → wfe E u → ok (E ++ (List.map (fun p => (p.1, subst_t Z u p.2)) F)) →
    wfe (E ++ (List.map (fun p => (p.1, subst_t Z u p.2)) F)) (subst_e Z u e)) := by
  sorry

/-- Coq: wft_subst -/ 
@[simp] theorem wft_subst : ∀ F Q E Z u T,
  wft (E ++ (Z, Q) :: F) T → (value u ∨ ∃ x, trm_fvar x = u) → wfe E u → ok (E ++ (List.map (fun p => (p.1, subst_t Z u p.2)) F)) →
  wft (E ++ (List.map (fun p => (p.1, subst_t Z u p.2)) F)) (subst_t Z u T) := by
  sorry

/-- Coq: wft_subst1 -/ 
@[simp] theorem wft_subst1 : ∀ F Q Z u T,
  wft ((Z, Q) :: F) T → (value u ∨ ∃ x, trm_fvar x = u) → wfe [] u → ok (List.map (fun p => (p.1, subst_t Z u p.2)) F) →
  wft (List.map (fun p => (p.1, subst_t Z u p.2)) F) (subst_t Z u T) := by
  sorry

/-- Coq: wft_subst_empty -/ 
@[simp] theorem wft_subst_empty : ∀ Q Z u T,
  wft [(Z, Q)] T → (value u ∨ ∃ x, trm_fvar x = u) → wfe [] u → wft [] (subst_t Z u T) := by
  sorry

/-- Coq: wft_open -/ 
@[simp] theorem wft_open : ∀ E u T1 T2,
  ok E → wft E (typ_all T1 T2) → (value u ∨ ∃ x, trm_fvar x = u) → wfe E u → wft E (open_t T2 u) := by
  sorry

-- Env relations and regularity
/-- Coq: ok_from_okt -/ 
@[simp] theorem ok_from_okt : ∀ E, okt E → ok E := by
  sorry

/-- Coq: wft_from_env_has -/ 
@[simp] theorem wft_from_env_has : ∀ x U E, okt E → binds x U E → wft E U := by
  sorry

/-- Coq: wft_from_okt -/ 
@[simp] theorem wft_from_okt : ∀ x T E, okt ((x, T) :: E) → wft E T := by
  sorry

/-- Coq: wft_weaken_right -/ 
@[simp] theorem wft_weaken_right : ∀ T E F, wft E T → ok (E ++ F) → wft (E ++ F) T := by
  sorry

/-- Coq: sub_has_regular -/ 
@[simp] theorem sub_has_regular :
  (∀ E S T, sub E S T → okt E ∧ wft E S ∧ wft E T) ∧
  (∀ E p T, has E p T → okt E ∧ wft E (typ_sel p) ∧ wft E T) := by
  sorry

/-- Coq: sub_regular -/ 
@[simp] theorem sub_regular : ∀ E S T, sub E S T → okt E ∧ wft E S ∧ wft E T := by
  sorry

/-- Coq: has_regular -/ 
@[simp] theorem has_regular : ∀ E p T, has E p T → okt E ∧ wft E (typ_sel p) ∧ wft E T := by
  sorry

/-- Coq: has_regular_e -/ 
@[simp] theorem has_regular_e : ∀ E p T, has E p T → (value p ∨ (∃ x, trm_fvar x = p)) ∧ wfe E p := by
  sorry

/-- Coq: typing_regular -/ 
@[simp] theorem typing_regular : ∀ E e T, typing E e T → okt E ∧ wfe E e ∧ wft E T := by
  sorry

/-- Coq: value_regular -/ 
@[simp] theorem value_regular : ∀ t, value t → def_term t := by
  sorry

/-- Coq: red_regular -/ 
@[simp] theorem red_regular : ∀ t t', red t t' → def_term t ∧ def_term t' := by
  sorry

-- Weakening/narrowing for sub/has
/-- Coq: sub_has_weakening -/ 
@[simp] theorem sub_has_weakening :
  (∀ E0 S T, sub E0 S T → ∀ E F G, E0 = E ++ G → okt (E ++ F ++ G) → sub (E ++ F ++ G) S T) ∧
  (∀ E0 p T, has E0 p T → ∀ E F G, E0 = E ++ G → okt (E ++ F ++ G) → has (E ++ F ++ G) p T) := by
  sorry

/-- Coq: sub_weakening -/ 
@[simp] theorem sub_weakening : ∀ E F G S T, sub (E ++ G) S T → okt (E ++ F ++ G) → sub (E ++ F ++ G) S T := by
  sorry

/-- Coq: has_weakening -/ 
@[simp] theorem has_weakening : ∀ E F G p T, has (E ++ G) p T → okt (E ++ F ++ G) → has (E ++ F ++ G) p T := by
  sorry

/-- Coq: sub_has_narrowing_aux -/ 
@[simp] theorem sub_has_narrowing_aux :
  (∀ E0 S T, sub E0 S T → ∀ Q E F z P, E0 = (E ++ (z, Q) :: F) → sub E P Q → sub (E ++ (z, P) :: F) S T) ∧
  (∀ E0 p T, has E0 p T → ∀ Q E F z P, E0 = (E ++ (z, Q) :: F) → sub E P Q → has (E ++ (z, P) :: F) p T) := by
  sorry

/-- Coq: sub_narrowing -/ 
@[simp] theorem sub_narrowing : ∀ Q E F Z P S T, sub E P Q → sub (E ++ (Z, Q) :: F) S T → sub (E ++ (Z, P) :: F) S T := by
  sorry

-- Substitution preserves subtyping
/-- Coq: has_value_var -/ 
@[simp] theorem has_value_var : ∀ E u T, has E u T → (value u ∨ ∃ x, trm_fvar x = u) := by
  sorry

/-- Coq: var_typing_has -/ 
@[simp] theorem var_typing_has : ∀ E x Q, typing E (trm_fvar x) Q → has E (trm_fvar x) Q := by
  sorry

/-- Coq: val_typing_has -/ 
@[simp] theorem val_typing_has : ∀ E u Q, value u → typing E u Q → has E u Q := by
  sorry

/-- Coq: sub_has_through_subst -/ 
@[simp] theorem sub_has_through_subst :
  (∀ E0 S T, sub E0 S T → ∀ Q E F Z u, E0 = (E ++ (Z, Q) :: F) → (value u ∨ ∃ x, trm_fvar x = u) → typing E u Q →
sub (E ++ (List.map (fun p => (p.1, subst_t Z u p.2)) F)) (subst_t Z u S) (subst_t Z u T)) ∧
  (∀ E0 p T, has E0 p T → ∀ Q E F Z u, E0 = (E ++ (Z, Q) :: F) → (value u ∨ ∃ x, trm_fvar x = u) → typing E u Q →
has (E ++ (List.map (fun p => (p.1, subst_t Z u p.2)) F)) (subst_e Z u p) (subst_t Z u T)) := by
  sorry

-- Typing properties
/-- Coq: typing_weakening -/ 
@[simp] theorem typing_weakening : ∀ E F G e T, typing (E ++ G) e T → okt (E ++ F ++ G) → typing (E ++ F ++ G) e T := by
  sorry

/-- Coq: typing_narrowing -/ 
@[simp] theorem typing_narrowing : ∀ Q E F X P e T, sub E P Q → typing (E ++ (X, Q) :: F) e T → typing (E ++ (X, P) :: F) e T := by
  sorry

/-- Coq: typing_through_subst -/ 
@[simp] theorem typing_through_subst : ∀ U E F z T e u, typing (E ++ (z, U) :: F) e T → (value u ∨ ∃ x, trm_fvar x = u) → typing E u U →
typing (E ++ (List.map (fun p => (p.1, subst_t z u p.2)) F)) (subst_e z u e) (subst_t z u T) := by
  sorry

/-- Coq: typing_through_subst1 -/ 
@[simp] theorem typing_through_subst1 : ∀ V y v e T, typing [(y, V)] e T → value v → typing [] v V → typing [] (subst_e y v e) (subst_t y v T) := by
  sorry

-- Canonical forms / results
/-- Coq: has_empty_value -/ 
@[simp] theorem has_empty_value : ∀ p T, has [] p T → value p := by
  sorry

/-- Coq: canonical_form_abs -/ 
@[simp] theorem canonical_form_abs : ∀ t U1 U2, value t → typing [] t (typ_all U1 U2) → ∃ V e1, t = trm_abs V e1 := by
  sorry

/-- Coq: canonical_form_mem -/ 
@[simp] theorem canonical_form_mem : ∀ t b T, value t → typing [] t (typ_mem b T) → ∃ V, t = trm_mem V := by
  sorry

-- Pseudo-subtyping and possible types framework
/-- Coq: psub_sub -/ 
@[simp] theorem psub_sub : ∀ S T, psub S T → sub [] S T := by
  sorry

/-- Coq: possible_types_value -/ 
@[simp] theorem possible_types_value : ∀ n p T, possible_types n p T → value p := by
  sorry

/-- Coq: possible_types_wfe -/ 
@[simp] theorem possible_types_wfe : ∀ n p T, possible_types n p T → wfe [] p := by
  sorry

/-- Coq: possible_types_wft -/ 
@[simp] theorem possible_types_wft : ∀ n p T, possible_types n p T → wft [] T := by
  sorry

/-- Coq: has_empty_var_false -/ 
@[simp] theorem has_empty_var_false : ∀ x T, has [] (trm_fvar x) T → False := by
  sorry

/-- Coq: possible_types_closure_psub -/ 
@[simp] theorem possible_types_closure_psub : ∀ n v T U, possible_types n v T → psub T U → possible_types n v U := by
  sorry

/-- Coq: psub_reflexivity -/ 
@[simp] theorem psub_reflexivity : ∀ T, wft [] T → psub T T := by
  sorry

/-- Coq: sub_psub_aux -/ 
@[simp] theorem sub_psub_aux :
  (∀ E S T, sub E S T → E = [] → psub S T) ∧
  (∀ E p T, has E p T → E = [] → possible_types 0 p T) := by
  sorry

/-- Coq: sub_psub -/ 
@[simp] theorem sub_psub : ∀ S T, sub [] S T → psub S T := by
  sorry

/-- Coq: possible_types_closure -/ 
@[simp] theorem possible_types_closure : ∀ n v T U, possible_types n v T → sub [] T U → possible_types n v U := by
  sorry

/-- Coq: possible_types_typing -/ 
@[simp] theorem possible_types_typing : ∀ v T, typing [] v T → value v → possible_types 1 v T := by
  sorry

/-- Coq: typing_inv_abs -/ 
@[simp] theorem typing_inv_abs :
  ∀ (S1 : typ) (e1 : trm) (T : typ), typing [] (trm_abs S1 e1) T →
    ∀ (U1 U2 : typ), sub [] T (typ_all U1 U2) →
      sub [] U1 S1 ∧ ∃ (S2 : typ) (L : Vars), ∀ (x : Var), x ∉ L →
        typing [(x, S1)] (open_e e1 (trm_fvar x)) (open_t S2 (trm_fvar x)) ∧
        sub [(x, U1)] (open_t S2 (trm_fvar x)) (open_t U2 (trm_fvar x)) := by
  sorry

/-- Coq: value_red_contra -/ 
@[simp] theorem value_red_contra : ∀ e e', value e → red e e' → False := by
  sorry

/-- Coq: preservation_result -/ 
@[simp] theorem preservation_result : preservation := by
  simp [preservation]
  sorry

/-- Coq: progress_result -/ 
@[simp] theorem progress_result : progress := by
  simp [progress]
  sorry

-- Placeholders to synchronize with Proof.progress.md (to be replaced with real statements)
-- Coq line 867
axiom okt_push_inv : Prop
-- Coq line 875
axiom okt_push_type : Prop
-- Coq line 883
axiom okt_narrow : Prop
-- Coq line 897
axiom okt_subst : Prop
-- Coq line 910
axiom okt_subst1 : Prop
-- Coq line 933
axiom notin_fv_open_rec : Prop
-- Coq line 943
axiom notin_fv_t_open : Prop
-- Coq line 950
axiom notin_fv_e_open : Prop
-- Coq line 957
axiom notin_fv_wf_rec : Prop
-- Coq line 969
axiom notin_fv_wf : Prop
-- Coq line 975
axiom map_subst_id : Prop
-- Coq line 1116
axiom sub_reflexivity : Prop
-- Coq line 1166
axiom sub_weakening1 : Prop
-- Coq line 1181
axiom sub_weakening_empty : Prop
-- Coq line 1204
axiom has_weakening1 : Prop
-- Coq line 1219
axiom has_weakening_empty : Prop
-- Coq line 1285
axiom sub_narrowing_empty : Prop
-- Coq line 1438
axiom typing_narrowing_empty : Prop

end Lp2lc.Active.Ddia
