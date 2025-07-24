import «Lp2lc».Active.FsubL_alt.Def
import «Lp2lc».Active.FsubL_alt.Auxiliary

namespace Lp2lc.Active.FsubL_alt

open typ trm bind

-- Properties of type substitution in type

-- Coq line 464: Lemma open_tt_rec_type_core
@[simp] theorem open_tt_rec_type_core : ∀ T j V U i, i ≠ j →
  (open_tt_rec j V T) = open_tt_rec i U (open_tt_rec j V T) →
  T = open_tt_rec i U T := by
  sorry -- TODO

-- Coq line 472: Lemma open_tt_rec_type
@[simp] theorem open_tt_rec_type : ∀ T U,
  def_type T → ∀ k, T = open_tt_rec k U T := by
  sorry -- TODO

-- Coq line 481: Lemma subst_tt_fresh
@[simp] theorem subst_tt_fresh : ∀ Z U T,
  Z ∉ fv_tt T → subst_tt Z U T = T := by
  sorry -- TODO

-- Coq line 490: Lemma subst_tt_open_tt_rec
@[simp] theorem subst_tt_open_tt_rec : ∀ T1 T2 X P n, def_type P →
  subst_tt X P (open_tt_rec n T2 T1) =
  open_tt_rec n (subst_tt X P T2) (subst_tt X P T1) := by
  sorry -- TODO

-- Coq line 500: Lemma subst_tt_open_tt
@[simp] theorem subst_tt_open_tt : ∀ T1 T2 X P, def_type P →
  subst_tt X P (open_tt T1 T2) =
  open_tt (subst_tt X P T1) (subst_tt X P T2) := by
  sorry -- TODO

-- Coq line 509: Lemma subst_tt_open_tt_var
@[simp] theorem subst_tt_open_tt_var : ∀ X Y U T, Y ≠ X → def_type U →
  open_tt (subst_tt X U T) (typ_fvar Y) = subst_tt X U (open_tt T (typ_fvar Y)) := by
  sorry -- TODO

-- Coq line 519: Lemma subst_tt_intro
@[simp] theorem subst_tt_intro : ∀ X T2 U,
  X ∉ fv_tt T2 → def_type U →
  open_tt T2 U = subst_tt X U (T2 open_tt_var X) := by
  sorry -- TODO

-- Properties of type substitution in terms

-- Coq line 531: Lemma open_te_rec_term_core
@[simp] theorem open_te_rec_term_core : ∀ e j u i P,
  open_ee_rec j u e = open_te_rec i P (open_ee_rec j u e) →
  e = open_te_rec i P e := by
  sorry -- TODO

-- Coq line 538: Lemma open_te_rec_type_core
@[simp] theorem open_te_rec_type_core : ∀ e j Q i P, i ≠ j →
  open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) →
  e = open_te_rec i P e := by
  sorry -- TODO

-- Coq line 547: Lemma open_te_rec_term
@[simp] theorem open_te_rec_term : ∀ e U,
  def_term e → ∀ k, e = open_te_rec k U e := by
  sorry -- TODO

-- Coq line 560: Lemma subst_te_fresh
@[simp] theorem subst_te_fresh : ∀ X U e,
  X ∉ fv_te e → subst_te X U e = e := by
  sorry -- TODO

-- Coq line 568: Lemma subst_te_open_te
@[simp] theorem subst_te_open_te : ∀ e T X U, def_type U →
  subst_te X U (open_te e T) =
  open_te (subst_te X U e) (subst_tt X U T) := by
  sorry -- TODO

-- Coq line 579: Lemma subst_te_open_te_var
@[simp] theorem subst_te_open_te_var : ∀ X Y U e, Y ≠ X → def_type U →
  open_te (subst_te X U e) (typ_fvar Y) = subst_te X U (open_te e (typ_fvar Y)) := by
  sorry -- TODO

-- Coq line 589: Lemma subst_te_intro
@[simp] theorem subst_te_intro : ∀ X U e,
  X ∉ fv_te e → def_type U →
  open_te e U = subst_te X U (e open_te_var X) := by
  sorry -- TODO

-- Properties of term substitution in terms

-- Coq line 601: Lemma open_ee_rec_term_core
@[simp] theorem open_ee_rec_term_core : ∀ e j v u i, i ≠ j →
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) →
  e = open_ee_rec i u e := by
  sorry -- TODO

-- Coq line 609: Lemma open_ee_rec_type_core
@[simp] theorem open_ee_rec_type_core' : ∀ e j V u i,
  open_te_rec j V e = open_ee_rec i u (open_te_rec j V e) →
  e = open_ee_rec i u e := by
  sorry -- TODO

-- Coq line 616: Lemma open_ee_rec_term
@[simp] theorem open_ee_rec_term : ∀ u e,
  def_term e → ∀ k, e = open_ee_rec k u e := by
  sorry -- TODO

-- Coq line 628: Lemma subst_ee_fresh
@[simp] theorem subst_ee_fresh : ∀ x u e,
  x ∉ fv_ee e → subst_ee x u e = e := by
  sorry -- TODO

-- Coq line 637: Lemma subst_ee_open_ee
@[simp] theorem subst_ee_open_ee : ∀ t1 t2 u x, def_term u →
  subst_ee x u (open_ee t1 t2) =
  open_ee (subst_ee x u t1) (subst_ee x u t2) := by
  sorry -- TODO

-- Coq line 649: Lemma subst_ee_open_ee_var
@[simp] theorem subst_ee_open_ee_var : ∀ x y u e, y ≠ x → def_term u →
  open_ee (subst_ee x u e) (trm_fvar y) =
  subst_ee x u (open_ee e (trm_fvar y)) := by
  sorry -- TODO

-- Coq line 659: Lemma subst_ee_intro
@[simp] theorem subst_ee_intro : ∀ x e u,
  x ∉ fv_ee e → def_term u →
  open_ee e u = subst_ee x u (open_ee e (trm_fvar x)) := by
  sorry -- TODO

-- Coq line 670: Lemma subst_te_open_ee_var
@[simp] theorem subst_te_open_ee_var : ∀ Z P x e,
  open_ee (subst_te Z P e) (trm_fvar x) = subst_te Z P (open_ee e (trm_fvar x)) := by
  sorry -- TODO

-- Coq line 680: Lemma subst_ee_open_te_var
@[simp] theorem subst_ee_open_te_var : ∀ z u e V, def_term u →
  open_te (subst_ee z u e) V = subst_ee z u (open_te e V) := by
  sorry -- TODO

-- Substitutions preserve local closure

-- Coq line 690: Lemma subst_tt_type
@[simp] theorem subst_tt_type : ∀ T Z P,
  def_type T → def_type P → def_type (subst_tt Z P T) := by
  sorry -- TODO

-- Coq line 698: Lemma subst_te_term
@[simp] theorem subst_te_term : ∀ e Z P,
  def_term e → def_type P → def_term (subst_te Z P e) := by
  sorry -- TODO

-- Coq line 706: Lemma subst_ee_term
@[simp] theorem subst_ee_term : ∀ e1 Z e2,
  def_term e1 → def_term e2 → def_term (subst_ee Z e2 e1) := by
  sorry -- TODO

-- Properties of well-formedness of a type in an environment

-- Coq line 723: Lemma wft_type
@[simp] theorem wft_type : ∀ E T,
  wft E T → def_type T := by
  sorry -- TODO

-- Coq line 731: Lemma wft_weaken
@[simp] theorem wft_weaken : ∀ G T E F,
  wft (E ++ G) T →
  ok (E ++ F ++ G) →
  wft (E ++ F ++ G) T := by
  sorry -- TODO

-- Coq line 744: Lemma wft_weaken_empty
@[simp] theorem wft_weaken_empty : ∀ T F,
  wft [] T →
  ok F →
  wft F T := by
  sorry -- TODO

-- Coq line 756: Lemma wft_narrow
@[simp] theorem wft_narrow : ∀ V0 V1 F U0 U1 T E X,
  wft (E ++ [(X, bind_sub V0 V1)] ++ F) T →
  ok (E ++ [(X, bind_sub U0 U1)] ++ F) →
  wft (E ++ [(X, bind_sub U0 U1)] ++ F) T := by
  sorry -- TODO

-- Coq line 773: Lemma wft_strengthen
@[simp] theorem wft_strengthen : ∀ E F x U T,
  wft (E ++ [(x, bind_typ U)] ++ F) T → wft (E ++ F) T := by
  sorry -- TODO

-- Coq line 790: Lemma wft_subst_tb
@[simp] theorem wft_subst_tb : ∀ F Q0 Q1 E Z P T,
  wft (E ++ [(Z, bind_sub Q0 Q1)] ++ F) T →
  wft E P →
  ok (E ++ map_subst_tb Z P F) →
  wft (E ++ map_subst_tb Z P F) (subst_tt Z P T) := by
  sorry -- TODO

-- Coq line 828: Lemma wft_open
@[simp] theorem wft_open : ∀ E U T0 T1 T2,
  ok E →
  wft E (typ_all T0 T1 T2) →
  wft E U →
  wft E (open_tt T2 U) := by
  sorry -- TODO

-- Relations between well-formed environment and types well-formed in environments

-- Helper lemma: binds is preserved by weakening (optional)
@[simp] theorem binds_weaken : ∀ x b E F G,
  binds x b (E ++ G) →
  binds x b (E ++ F ++ G) := by
  sorry -- TODO

-- Coq line 847: Lemma ok_from_okt
@[simp] theorem ok_from_okt : ∀ E,
  okt E → ok E := by
  sorry -- TODO

-- Coq line 857: Lemma wft_from_env_has_sub
@[simp] theorem wft_from_env_has_sub : ∀ x U0 U1 E,
  okt E → binds x (bind_sub U0 U1) E → wft E U0 ∧ wft E U1 := by
  sorry -- TODO

-- Coq line 876: Lemma wft_from_env_has_typ
@[simp] theorem wft_from_env_has_typ : ∀ x U E,
  okt E → binds x (bind_typ U) E → wft E U := by
  sorry -- TODO

-- Coq line 895: Lemma wft_from_okt_typ
@[simp] theorem wft_from_okt_typ : ∀ x T E,
  okt ((x, bind_typ T) :: E) → wft E T := by
  sorry -- TODO

-- Coq line 904: Lemma wft_from_okt_sub
@[simp] theorem wft_from_okt_sub : ∀ x T0 T1 E,
  okt ((x, bind_sub T0 T1) :: E) → wft E T0 ∧ wft E T1 := by
  sorry -- TODO

-- Coq line 915: Lemma wft_weaken_right
@[simp] theorem wft_weaken_right : ∀ T E F,
  wft E T →
  ok (E ++ F) →
  wft (E ++ F) T := by
  sorry -- TODO

-- Environment regularity and automation

-- Coq line 1041: Lemma notin_fv_tt_open
@[simp] theorem notin_fv_tt_open : ∀ Y X T,
  X ∉ fv_tt (T open_tt_var Y) →
  X ∉ fv_tt T := by
  sorry -- TODO

-- Coq line 1051: Lemma notin_fv_wf
@[simp] theorem notin_fv_wf : ∀ E X T,
  wft E T → X ∉ dom E → X ∉ fv_tt T := by
  sorry -- TODO

-- Coq line 1062: Lemma map_subst_tb_id
@[simp] theorem map_subst_tb_id : ∀ G Z P,
  okt G → Z ∉ dom G → G = map_subst_tb Z P G := by
  sorry -- TODO

-- Regularity

-- Coq line 1079: Lemma sub_regular
@[simp] theorem sub_regular : ∀ E S T,
  sub E S T → okt E ∧ wft E S ∧ wft E T := by
  sorry -- TODO

-- Coq line 1098: Lemma typing_regular
@[simp] theorem typing_regular : ∀ E e T,
  typing E e T → okt E ∧ def_term e ∧ wft E T := by
  sorry -- TODO

-- Coq line 1141: Lemma value_regular
@[simp] theorem value_regular : ∀ t,
  value t → def_term t := by
  sorry -- TODO

-- Coq line 1149: Lemma red_regular
@[simp] theorem red_regular : ∀ t t',
  red t t' → def_term t ∧ def_term t' := by
  sorry -- TODO

-- Subtyping properties

-- Coq line 1201: Lemma sub_reflexivity
@[simp] theorem sub_reflexivity : ∀ E T,
  okt E →
  wft E T →
  sub E T T := by
  sorry -- TODO

-- Coq line 1214: Lemma sub_weakening
@[simp] theorem sub_weakening : ∀ E F G S T,
  sub (E ++ G) S T →
  okt (E ++ F ++ G) →
  sub (E ++ F ++ G) S T := by
  sorry -- TODO

-- Coq line 1230: Lemma sub_weakening_empty
@[simp] theorem sub_weakening_empty : ∀ F G S T,
  sub G S T →
  okt (F ++ G) →
  sub (F ++ G) S T := by
  sorry -- TODO

-- Coq line 1247: Lemma sub_narrowing_aux
@[simp] theorem sub_narrowing_aux : ∀ Q0 Q1 F E Z P0 P1 S T,
  sub (E ++ [(Z, bind_sub Q0 Q1)] ++ F) S T →
  sub E Q0 P0 →
  sub E P1 Q1 →
  sub (E ++ [(Z, bind_sub P0 P1)] ++ F) S T := by
  sorry -- TODO

-- Coq line 1284: Lemma sub_narrowing
@[simp] theorem sub_narrowing : ∀ Q0 Q1 E F Z P0 P1 S T,
  sub E Q0 P0 →
  sub E P1 Q1 →
  sub (E ++ [(Z, bind_sub Q0 Q1)] ++ F) S T →
  sub (E ++ [(Z, bind_sub P0 P1)] ++ F) S T := by
  sorry -- TODO

-- Coq line 1294: Lemma sub_narrowing_empty
@[simp] theorem sub_narrowing_empty : ∀ Q0 Q1 Z P0 P1 S T,
  sub [] Q0 P0 →
  sub [] P1 Q1 →
  sub ([(Z, bind_sub Q0 Q1)]) S T →
  sub ([(Z, bind_sub P0 P1)]) S T := by
  sorry -- TODO

-- Coq line 1312: Lemma sub_through_subst_tt
@[simp] theorem sub_through_subst_tt : ∀ Q0 Q1 E F Z S T P,
  sub (E ++ [(Z, bind_sub Q0 Q1)] ++ F) S T →
  sub E Q0 P →
  sub E P Q1 →
  sub (E ++ map_subst_tb Z P F) (subst_tt Z P S) (subst_tt Z P T) := by
  sorry -- TODO

-- Typing properties

-- Coq line 1372: Lemma typing_weakening
@[simp] theorem typing_weakening : ∀ E F G e T,
  typing (E ++ G) e T →
  okt (E ++ F ++ G) →
  typing (E ++ F ++ G) e T := by
  sorry -- TODO

-- Coq line 1396: Lemma sub_strengthening
@[simp] theorem sub_strengthening : ∀ x U E F S T,
  sub (E ++ [(x, bind_typ U)] ++ F) S T →
  sub (E ++ F) S T := by
  sorry -- TODO

-- Coq line 1415: Lemma typing_narrowing
@[simp] theorem typing_narrowing : ∀ Q0 Q1 E F X P0 P1 e T,
  sub E Q0 P0 →
  sub E P1 Q1 →
  sub E P0 P1 →
  typing (E ++ [(X, bind_sub Q0 Q1)] ++ F) e T →
  typing (E ++ [(X, bind_sub P0 P1)] ++ F) e T := by
  sorry -- TODO

-- Coq line 1432: Lemma typing_narrowing_empty
@[simp] theorem typing_narrowing_empty : ∀ Q0 Q1 X P0 P1 e T,
  sub [] Q0 P0 →
  sub [] P1 Q1 →
  sub [] P0 P1 →
  typing ([(X, bind_sub Q0 Q1)]) e T →
  typing ([(X, bind_sub P0 P1)]) e T := by
  sorry -- TODO

-- Coq line 1449: Lemma typing_through_subst_ee
@[simp] theorem typing_through_subst_ee : ∀ U E F x T e u,
  typing (E ++ [(x, bind_typ U)] ++ F) e T →
  typing E u U →
  typing (E ++ F) (subst_ee x u e) T := by
  sorry -- TODO

-- Coq line 1472: Lemma typing_through_subst_te
@[simp] theorem typing_through_subst_te : ∀ Q0 Q1 E F Z e T P,
  typing (E ++ [(Z, bind_sub Q0 Q1)] ++ F) e T →
  sub E Q0 P →
  sub E P Q1 →
  typing (E ++ map_subst_tb Z P F) (subst_te Z P e) (subst_tt Z P T) := by
  sorry -- TODO

-- Preservation and possible types

-- Coq line 1512: Inductive possible_types and derived lemmas
@[simp] theorem possible_types_value : ∀ p T,
  possible_types p T →
  value p := by
  sorry -- TODO

@[simp] theorem possible_types_closure : ∀ v T U,
  possible_types v T →
  sub [] T U →
  possible_types v U := by
  sorry -- TODO

@[simp] theorem possible_types_typing : ∀ v T,
  typing [] v T → value v →
  possible_types v T := by
  sorry -- TODO

-- Inversion lemmas

@[simp] theorem typing_inv_abs : ∀ S1 e1 T,
  typing [] (trm_abs S1 e1) T →
  ∀ U1 U2, sub [] T (typ_arrow U1 U2) →
     sub [] U1 S1 ∧ ∃ S2, ∃ L : Vars, ∀ x, x ∉ L →
     typing ([(x, bind_typ S1)]) (open_ee e1 (trm_fvar x)) S2 ∧ sub [] S2 U2 := by
  sorry -- TODO

@[simp] theorem typing_inv_tabs : ∀ S10 S11 e1 T,
  typing [] (trm_tabs S10 S11 e1) T →
  ∀ U10 U11 U2, sub [] T (typ_all U10 U11 U2) → sub [] U10 U11 →
     sub [] S10 U10 ∧ sub [] U11 S11 ∧
     ∃ S2, ∃ L : Vars, ∀ X, X ∉ L →
     typing ([(X, bind_sub U10 U11)]) (open_te e1 (typ_fvar X)) (open_tt S2 (typ_fvar X)) ∧
     sub ([(X, bind_sub U10 U11)]) (open_tt S2 (typ_fvar X)) (open_tt U2 (typ_fvar X)) := by
  sorry -- TODO

-- Coq line 1624: Preservation result
@[simp] theorem preservation_result : preservation := by
  sorry -- TODO

-- Progress and canonical forms

-- Coq line 1660: value_not_bot
@[simp] theorem value_not_bot : ∀ t T,
  value t → typing [] t T → T ≠ typ_bot := by
  sorry -- TODO

-- Coq line 1668: canonical_form_abs
@[simp] theorem canonical_form_abs : ∀ t U1 U2,
  value t → typing [] t (typ_arrow U1 U2) →
  ∃ V, ∃ e1, t = trm_abs V e1 := by
  sorry -- TODO

-- Coq line 1678: canonical_form_tabs
@[simp] theorem canonical_form_tabs : ∀ t U0 U1 U2,
  value t → typing [] t (typ_all U0 U1 U2) →
  ∃ V0 V1, ∃ e1, t = trm_tabs V0 V1 e1 := by
  sorry -- TODO

-- Coq line 1691: progress_result
@[simp] theorem progress_result : progress := by
  sorry -- TODO

end Lp2lc.Active.FsubL_alt
