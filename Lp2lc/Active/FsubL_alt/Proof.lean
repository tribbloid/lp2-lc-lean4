import «Lp2lc».Active.FsubL_alt.Def
import «Lp2lc».Active.FsubL_alt.Auxiliary

namespace Lp2lc.Active.FsubL_alt

open typ trm bind

-- Substitution and opening lemmas on types
/-- Coq: open_tt_rec_type_core -/ 
theorem open_tt_rec_type_core : ∀ T j V U i, i ≠ j →
  open_tt_rec j V T = open_tt_rec i U (open_tt_rec j V T) →
  T = open_tt_rec i U T := by
  sorry

/-- Coq: open_tt_rec_type -/
theorem open_tt_rec_type : ∀ T U, def_type T → ∀ k, T = open_tt_rec k U T := by
  sorry

/-- Coq: subst_tt_fresh -/
theorem subst_tt_fresh : ∀ Z U T,
  Z ∉ fv_tt T → subst_tt Z U T = T := by
  sorry

/-- Coq: subst_tt_open_tt_rec -/
theorem subst_tt_open_tt_rec : ∀ T1 T2 X P n, def_type P →
  subst_tt X P (open_tt_rec n T2 T1) =
  open_tt_rec n (subst_tt X P T2) (subst_tt X P T1) := by
  sorry

/-- Coq: subst_tt_open_tt -/
theorem subst_tt_open_tt : ∀ T1 T2 X P, def_type P →
  subst_tt X P (open_tt T1 T2) =
  open_tt (subst_tt X P T1) (subst_tt X P T2) := by
  sorry

/-- Coq: subst_tt_open_tt_var -/
theorem subst_tt_open_tt_var : ∀ X Y U T, Y ≠ X → def_type U →
  open_tt (subst_tt X U T) (typ_fvar Y) = subst_tt X U (open_tt T (typ_fvar Y)) := by
  sorry

/-- Coq: subst_tt_intro -/
theorem subst_tt_intro : ∀ X T2 U,
  X ∉ fv_tt T2 → def_type U →
  open_tt T2 U = subst_tt X U (T2 open_tt_var X) := by
  sorry

-- Substitution and opening lemmas on terms (type- and term-level)
/-- Coq: open_te_rec_term_core -/
theorem open_te_rec_term_core : ∀ e j u i P,
  open_ee_rec j u e = open_te_rec i P (open_ee_rec j u e) →
  e = open_te_rec i P e := by
  sorry

/-- Coq: open_te_rec_type_core -/
theorem open_te_rec_type_core : ∀ e j Q i P, i ≠ j →
  open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) →
  e = open_te_rec i P e := by
  sorry

/-- Coq: open_te_rec_term -/
theorem open_te_rec_term : ∀ e U,
  def_term e → ∀ k, e = open_te_rec k U e := by
  sorry

/-- Coq: subst_te_fresh -/
theorem subst_te_fresh : ∀ X U e,
  X ∉ fv_te e → subst_te X U e = e := by
  sorry

/-- Coq: subst_te_open_te -/
theorem subst_te_open_te : ∀ e T X U, def_type U →
  subst_te X U (open_te e T) =
  open_te (subst_te X U e) (subst_tt X U T) := by
  sorry

/-- Coq: subst_te_open_te_var -/
theorem subst_te_open_te_var : ∀ X Y U e, Y ≠ X → def_type U →
  open_te (subst_te X U e) (typ_fvar Y) = subst_te X U (open_te e (typ_fvar Y)) := by
  sorry

/-- Coq: subst_te_intro -/
theorem subst_te_intro : ∀ X U e,
  X ∉ fv_te e → def_type U →
  open_te e U = subst_te X U (e open_te_var X) := by
  sorry

/-- Coq: open_ee_rec_term_core -/
theorem open_ee_rec_term_core : ∀ e j v u i, i ≠ j →
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) →
  e = open_ee_rec i u e := by
  sorry

/-- Coq: open_ee_rec_type_core -/
theorem open_ee_rec_type_core : ∀ e j V u i,
  open_te_rec j V e = open_ee_rec i u (open_te_rec j V e) →
  e = open_ee_rec i u e := by
  sorry

/-- Coq: open_ee_rec_term -/
theorem open_ee_rec_term : ∀ u e,
  def_term e → ∀ k, e = open_ee_rec k u e := by
  sorry

/-- Coq: subst_ee_fresh -/
theorem subst_ee_fresh : ∀ x u e,
  x ∉ fv_ee e → subst_ee x u e = e := by
  sorry

/-- Coq: subst_ee_open_ee -/
theorem subst_ee_open_ee : ∀ t1 t2 u x, def_term u →
  subst_ee x u (open_ee t1 t2) =
  open_ee (subst_ee x u t1) (subst_ee x u t2) := by
  sorry

/-- Coq: subst_ee_open_ee_var -/
theorem subst_ee_open_ee_var : ∀ x y u e, y ≠ x → def_term u →
  open_ee (subst_ee x u e) (trm_fvar y) =
  subst_ee x u (open_ee e (trm_fvar y)) := by
  sorry

/-- Coq: subst_ee_open_te_var -/
theorem subst_ee_open_te_var : ∀ z u e V, def_term u →
  open_te (subst_ee z u e) V = subst_ee z u (open_te e V) := by
  sorry

/-- Coq: subst_ee_intro -/
theorem subst_ee_intro : ∀ x e u,
  x ∉ fv_ee e → def_term u →
  open_ee e u = subst_ee x u (open_ee e (trm_fvar x)) := by
  sorry

-- Substitutions preserve local closure
/-- Coq: subst_tt_type -/
theorem subst_tt_type : ∀ T Z P,
  def_type T → def_type P → def_type (subst_tt Z P T) := by
  sorry

/-- Coq: subst_te_term -/
theorem subst_te_term : ∀ e Z P,
  def_term e → def_type P → def_term (subst_te Z P e) := by
  sorry

/-- Coq: subst_ee_term -/
theorem subst_ee_term : ∀ e1 Z e2,
  def_term e1 → def_term e2 → def_term (subst_ee Z e2 e1) := by
  sorry

-- WFT and environment structure lemmas
/-- Coq: wft_type -/
theorem wft_type : ∀ E T,
  wft E T → def_type T := by
  sorry

/-- Coq: wft_weaken -/
theorem wft_weaken : ∀ G T E F,
  wft (E ++ G) T →
  ok (E ++ F ++ G) →
  wft (E ++ F ++ G) T := by
  sorry

/-- Coq: wft_narrow -/
theorem wft_narrow : ∀ V0 V1 F U0 U1 T E X,
  wft (E ++ [(X, bind_sub V0 V1)] ++ F) T →
  ok (E ++ [(X, bind_sub U0 U1)] ++ F) →
  wft (E ++ [(X, bind_sub U0 U1)] ++ F) T := by
  sorry

/-- Coq: wft_strengthen -/
theorem wft_strengthen : ∀ E F x U T,
 wft (E ++ [(x, bind_typ U)] ++ F) T → wft (E ++ F) T := by
  sorry

/-- Coq: wft_subst_tb -/
theorem wft_subst_tb : ∀ F Q0 Q1 E Z P T,
  wft (E ++ [(Z, bind_sub Q0 Q1)] ++ F) T →
  wft E P →
  ok (E ++ map_subst_tb Z P F) →
  wft (E ++ map_subst_tb Z P F) (subst_tt Z P T) := by
  sorry

/-- Coq: wft_subst_tb_empty -/
theorem wft_subst_tb_empty : ∀ F Q0 Q1 Z P T,
  wft ([(Z, bind_sub Q0 Q1)] ++ F) T →
  wft [] P →
  ok (map_subst_tb Z P F) →
  wft (map_subst_tb Z P F) (subst_tt Z P T) := by
  sorry

/-- Coq: wft_open -/
theorem wft_open : ∀ E U T0 T1 T2,
  ok E →
  wft E (typ_all T0 T1 T2) →
  wft E U →
  wft E (open_tt T2 U) := by
  sorry

/-- Coq: ok_from_okt -/
theorem ok_from_okt : ∀ E,
  okt E → ok E := by
  sorry

/-- Coq: wft_from_env_has_sub -/
theorem wft_from_env_has_sub : ∀ x U0 U1 E,
  okt E → binds x (bind_sub U0 U1) E → wft E U0 ∧ wft E U1 := by
  sorry

/-- Coq: wft_from_env_has_typ -/
theorem wft_from_env_has_typ : ∀ x U E,
  okt E → binds x (bind_typ U) E → wft E U := by
  sorry

/-- Coq: wft_from_okt_typ -/
theorem wft_from_okt_typ : ∀ x T E,
  okt ((x, bind_typ T) :: E) → wft E T := by
  sorry

/-- Coq: wft_from_okt_sub -/
theorem wft_from_okt_sub : ∀ x T0 T1 E,
  okt ((x, bind_sub T0 T1) :: E) → wft E T0 ∧ wft E T1 := by
  sorry

/-- Coq: wft_weaken_right -/
theorem wft_weaken_right : ∀ T E F,
  wft E T →
  ok (E ++ F) →
  wft (E ++ F) T := by
  sorry

-- Environment lemmas
/-- Coq: okt_push_inv -/
theorem okt_push_inv : ∀ E X B,
  okt ((X, B) :: E) → (∃ T0 T1, B = bind_sub T0 T1) ∨ (∃ T, B = bind_typ T) := by
  sorry

/-- Coq: okt_push_sub_inv -/
theorem okt_push_sub_inv : ∀ E X T0 T1,
  okt ((X, bind_sub T0 T1) :: E) → okt E ∧ wft E T0 ∧ wft E T1 ∧ E.lookup X = none := by
  sorry

/-- Coq: okt_push_sub_type -/
theorem okt_push_sub_type : ∀ E X T0 T1,
  okt ((X, bind_sub T0 T1) :: E) → def_type T0 ∧ def_type T1 := by
  sorry

/-- Coq: okt_push_typ_inv -/
theorem okt_push_typ_inv : ∀ E x T,
  okt ((x, bind_typ T) :: E) → okt E ∧ wft E T ∧ E.lookup x = none := by
  sorry

/-- Coq: okt_push_typ_type -/
theorem okt_push_typ_type : ∀ E X T,
  okt ((X, bind_typ T) :: E) → def_type T := by
  sorry

/-- Coq: okt_narrow -/
theorem okt_narrow : ∀ V0 V1 (E F : env) U0 U1 X,
  okt (E ++ [(X, bind_sub V0 V1)] ++ F) →
  wft E U0 → wft E U1 →
  okt (E ++ [(X, bind_sub U0 U1)] ++ F) := by
  sorry

/-- Coq: okt_strengthen -/
theorem okt_strengthen : ∀ x T (E F : env),
  okt (E ++ [(x, bind_typ T)] ++ F) →
  okt (E ++ F) := by
  sorry

/-- Coq: okt_subst_tb -/
theorem okt_subst_tb : ∀ Q0 Q1 Z P (E F : env),
  okt (E ++ [(Z, bind_sub Q0 Q1)] ++ F) →
  wft E P →
  okt (E ++ map_subst_tb Z P F) := by
  sorry

/-- Coq: okt_subst_tb_empty -/
theorem okt_subst_tb_empty : ∀ Q0 Q1 Z P (F : env),
  okt ([(Z, bind_sub Q0 Q1)] ++ F) →
  wft [] P →
  okt (map_subst_tb Z P F) := by
  sorry

-- Freshness and FV lemmas
/-- Coq: notin_fv_tt_open -/
theorem notin_fv_tt_open : ∀ Y X T,
  X ∉ fv_tt (T open_tt_var Y) →
  X ∉ fv_tt T := by
  sorry

/-- Coq: notin_fv_wf -/
theorem notin_fv_wf : ∀ E X T,
  wft E T → X ∉ Env.dom E → X ∉ fv_tt T := by
  sorry

/-- Coq: map_subst_tb_id -/
theorem map_subst_tb_id : ∀ G Z P,
  okt G → Z ∉ Env.dom G → G = map_subst_tb Z P G := by
  sorry

-- Regularity of relations
/-- Coq: sub_regular -/
theorem sub_regular : ∀ E S T,
  sub E S T → okt E ∧ wft E S ∧ wft E T := by
  sorry

/-- Coq: typing_regular -/
theorem typing_regular : ∀ E e T,
  typing E e T → okt E ∧ def_term e ∧ wft E T := by
  sorry

/-- Coq: value_regular -/
theorem value_regular : ∀ t,
  value t → def_term t := by
  sorry

/-- Coq: red_regular -/
theorem red_regular : ∀ t t',
  red t t' → def_term t ∧ def_term t' := by
  sorry

-- Properties of subtyping and typing
/-- Coq: sub_reflexivity -/
theorem sub_reflexivity : ∀ E T,
  okt E → wft E T → sub E T T := by
  sorry

/-- Coq: sub_weakening -/
theorem sub_weakening : ∀ E F G S T,
   sub (E ++ G) S T →
   okt (E ++ F ++ G) →
   sub (E ++ F ++ G) S T := by
  sorry

/-- Coq: sub_narrowing_aux -/
theorem sub_narrowing_aux : ∀ Q0 Q1 F E Z P0 P1 S T,
  sub (E ++ [(Z, bind_sub Q0 Q1)] ++ F) S T →
  sub E Q0 P0 →
  sub E P1 Q1 →
  sub (E ++ [(Z, bind_sub P0 P1)] ++ F) S T := by
  sorry

/-- Coq: sub_narrowing -/
theorem sub_narrowing : ∀ Q0 Q1 E F Z P0 P1 S T,
  sub E Q0 P0 →
  sub E P1 Q1 →
  sub (E ++ [(Z, bind_sub Q0 Q1)] ++ F) S T →
  sub (E ++ [(Z, bind_sub P0 P1)] ++ F) S T := by
  sorry

/-- Coq: sub_through_subst_tt -/
theorem sub_through_subst_tt : ∀ Q0 Q1 E F Z S T P,
  sub (E ++ [(Z, bind_sub Q0 Q1)] ++ F) S T →
  sub E Q0 P →
  sub E P Q1 →
  sub (E ++ map_subst_tb Z P F) (subst_tt Z P S) (subst_tt Z P T) := by
  sorry

/-- Coq: typing_weakening -/
theorem typing_weakening : ∀ E F G e T,
   typing (E ++ G) e T →
   okt (E ++ F ++ G) →
   typing (E ++ F ++ G) e T := by
  sorry

/-- Coq: sub_strengthening -/
theorem sub_strengthening : ∀ x U E F S T,
  sub (E ++ [(x, bind_typ U)] ++ F) S T →
  sub (E ++ F) S T := by
  sorry

/-- Coq: typing_narrowing -/
theorem typing_narrowing : ∀ Q0 Q1 E F X P0 P1 e T,
  sub E Q0 P0 → sub E P1 Q1 → sub E P0 P1 →
  typing (E ++ [(X, bind_sub Q0 Q1)] ++ F) e T →
  typing (E ++ [(X, bind_sub P0 P1)] ++ F) e T := by
  sorry

/-- Coq: typing_through_subst_ee -/
theorem typing_through_subst_ee : ∀ U E F x T e u,
  typing (E ++ [(x, bind_typ U)] ++ F) e T →
  typing E u U →
  typing (E ++ F) (subst_ee x u e) T := by
  sorry

/-- Coq: typing_through_subst_te -/
theorem typing_through_subst_te : ∀ Q0 Q1 E F Z e T P,
  typing (E ++ [(Z, bind_sub Q0 Q1)] ++ F) e T →
  sub E Q0 P → sub E P Q1 →
  typing (E ++ map_subst_tb Z P F) (subst_te Z P e) (subst_tt Z P T) := by
  sorry

-- Canonical forms and meta results
/-- Coq: value_not_bot -/
theorem value_not_bot : ∀ t T,
  value t → typing [] t T → T ≠ typ_bot := by
  sorry

/-- Coq: canonical_form_abs -/
theorem canonical_form_abs : ∀ t U1 U2,
  value t → typing [] t (typ_arrow U1 U2) →
  ∃ V e1, t = trm_abs V e1 := by
  sorry

/-- Coq: canonical_form_tabs -/
theorem canonical_form_tabs : ∀ t U0 U1 U2,
  value t → typing [] t (typ_all U0 U1 U2) →
  ∃ V0 V1 e1, t = trm_tabs V0 V1 e1 := by
  sorry

/-- Coq: preservation_result -/
theorem preservation_result : preservation := by
  simp [preservation]
  sorry

/-- Coq: progress_result -/
theorem progress_result : progress := by
  simp [progress]
  sorry

end Lp2lc.Active.FsubL_alt
