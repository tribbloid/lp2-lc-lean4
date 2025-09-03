/-***************************************************************************
* Preservation and Progress for System-F with Subtyping - Proofs           *
***************************************************************************-/

import «Lp2lc».Active.Fsub.Def

namespace Lp2lc.Active

open typ trm bind

-- Properties of type substitution in type

-- Coq line 430: Lemma open_tt_rec_type_core
theorem open_tt_rec_type_core : ∀ T j V U i, i ≠ j →
  (open_tt_rec j V T) = open_tt_rec i U (open_tt_rec j V T) →
  T = open_tt_rec i U T := by
  sorry -- Complex proof with many cases

-- Coq line 438: Lemma open_tt_rec_type
theorem open_tt_rec_type : ∀ T U,
  def_type T → ∀ k, T = open_tt_rec k U T := by
  sorry -- Complex proof with cofinite reasoning

-- Coq line 447: Lemma subst_tt_fresh
theorem subst_tt_fresh : ∀ Z U T,
  Z ∉ fv_tt T → subst_tt Z U T = T := by
  intro Z U T
  induction T with
  | typ_top => intro _; simp [subst_tt]
  | typ_bvar n => intro _; simp [subst_tt]
  | typ_fvar X => 
    intro h
    simp [fv_tt] at h
    simp only [subst_tt]
    split_ifs with heq
    · subst heq; simp at h
    · rfl
  | typ_arrow T1 T2 ih1 ih2 =>
    intro h
    simp [fv_tt] at h
    simp [subst_tt, ih1 h.1, ih2 h.2]
  | typ_all T1 T2 ih1 ih2 =>
    intro h
    simp [fv_tt] at h
    simp [subst_tt, ih1 h.1, ih2 h.2]

-- Coq line 456: Lemma subst_tt_open_tt_rec
theorem subst_tt_open_tt_rec : ∀ T1 T2 X P n, def_type P →
  subst_tt X P (open_tt_rec n T2 T1) =
  open_tt_rec n (subst_tt X P T2) (subst_tt X P T1) := by
  sorry -- Complex proof involving split_ifs

-- Coq line 466: Lemma subst_tt_open_tt
theorem subst_tt_open_tt : ∀ T1 T2 X P, def_type P →
  subst_tt X P (open_tt T1 T2) =
  open_tt (subst_tt X P T1) (subst_tt X P T2) := by
  intro T1 T2 X P HP
  simp only [open_tt]
  exact subst_tt_open_tt_rec T1 T2 X P 0 HP

-- Coq line 476: Lemma subst_tt_open_tt_var
theorem subst_tt_open_tt_var : ∀ X Y U T, Y ≠ X → def_type U →
  open_tt (subst_tt X U T) (typ_fvar Y) = subst_tt X U (open_tt T (typ_fvar Y)) := by
  intro X Y U T Hneq HU
  rw [subst_tt_open_tt _ _ _ _ HU]
  simp only [subst_tt]
  split_ifs with h
  · subst h; contradiction
  · rfl

-- Coq line 486: Lemma subst_tt_intro
theorem subst_tt_intro : ∀ X T2 U,
  X ∉ fv_tt T2 → def_type U →
  open_tt T2 U = subst_tt X U (T2 open_tt_var X) := by
  intro X T2 U Hfresh HU
  rw [subst_tt_open_tt _ _ _ _ HU]
  simp only [subst_tt]
  split_ifs with h
  · congr 1
    exact (subst_tt_fresh X U T2 Hfresh).symm
  · contradiction

-- Properties of type substitution in terms

-- Coq line 498: Lemma open_te_rec_term_core
theorem open_te_rec_term_core : ∀ e j u i P,
  open_ee_rec j u e = open_te_rec i P (open_ee_rec j u e) →
  e = open_te_rec i P e := by
  sorry

-- Coq line 505: Lemma open_te_rec_type_core
theorem open_te_rec_type_core : ∀ e j Q i P, i ≠ j →
  open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) →
  e = open_te_rec i P e := by
  sorry

-- Coq line 514: Lemma open_te_rec_term
theorem open_te_rec_term : ∀ e U,
  def_term e → ∀ k, e = open_te_rec k U e := by
  sorry -- Need to handle ℕ vs Var type mismatch

-- Coq line 527: Lemma subst_te_fresh
theorem subst_te_fresh : ∀ X U e,
  X ∉ fv_te e → subst_te X U e = e := by
  intro X U e
  induction e with
  | trm_bvar n => intro _; simp [subst_te]
  | trm_fvar x => intro _; simp [subst_te]
  | trm_abs V e1 ih =>
    intro h
    simp [fv_te] at h
    simp [subst_te, subst_tt_fresh X U V h.1, ih h.2]
  | trm_app e1 e2 ih1 ih2 =>
    intro h
    simp [fv_te] at h
    simp [subst_te, ih1 h.1, ih2 h.2]
  | trm_tabs V e1 ih =>
    intro h
    simp [fv_te] at h
    simp [subst_te, subst_tt_fresh X U V h.1, ih h.2]
  | trm_tapp e1 V ih =>
    intro h
    simp [fv_te] at h
    simp [subst_te, subst_tt_fresh X U V h.1, ih h.2]

-- Coq line 535: Lemma subst_te_open_te
theorem subst_te_open_te : ∀ e T X U, def_type U →
  subst_te X U (open_te e T) =
  open_te (subst_te X U e) (subst_tt X U T) := by
  sorry

-- Coq line 546: Lemma subst_te_open_te_var
theorem subst_te_open_te_var : ∀ X Y U e, Y ≠ X → def_type U →
  open_te (subst_te X U e) (typ_fvar Y) = subst_te X U (open_te e (typ_fvar Y)) := by
  sorry

-- Coq line 556: Lemma subst_te_intro
theorem subst_te_intro : ∀ X U e,
  X ∉ fv_te e → def_type U →
  open_te e U = subst_te X U (e open_te_var X) := by
  sorry

-- Properties of term substitution in terms

-- Coq line 568: Lemma open_ee_rec_term_core
theorem open_ee_rec_term_core : ∀ e j v u i, i ≠ j →
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) →
  e = open_ee_rec i u e := by
  sorry -- Complex case analysis on bound variables

-- Coq line 576: Lemma open_ee_rec_type_core'
theorem open_ee_rec_type_core' : ∀ e j V u i,
  open_te_rec j V e = open_ee_rec i u (open_te_rec j V e) →
  e = open_ee_rec i u e := by
  sorry

-- Coq line 583: Lemma open_ee_rec_term
theorem open_ee_rec_term : ∀ u e,
  def_term e → ∀ k, e = open_ee_rec k u e := by
  sorry -- Need to handle ℕ vs Var type mismatch

-- Coq line 595: Lemma subst_ee_fresh
theorem subst_ee_fresh : ∀ x u e,
  x ∉ fv_ee e → subst_ee x u e = e := by
  intro x u e
  induction e with
  | trm_bvar n => intro _; simp [subst_ee]
  | trm_fvar y =>
    intro h
    simp [fv_ee] at h
    simp only [subst_ee]
    split_ifs with heq
    · subst heq; simp at h
    · rfl
  | trm_abs V e1 ih =>
    intro h
    simp [fv_ee] at h
    simp [subst_ee, ih h]
  | trm_app e1 e2 ih1 ih2 =>
    intro h
    simp [fv_ee] at h
    simp [subst_ee, ih1 h.1, ih2 h.2]
  | trm_tabs V e1 ih =>
    intro h
    simp [fv_ee] at h
    simp [subst_ee, ih h]
  | trm_tapp e1 V ih =>
    intro h
    simp [fv_ee] at h
    simp [subst_ee, ih h]

-- Coq line 604: Lemma subst_ee_open_ee
theorem subst_ee_open_ee : ∀ t1 t2 u x, def_term u →
  subst_ee x u (open_ee t1 t2) =
  open_ee (subst_ee x u t1) (subst_ee x u t2) := by
  sorry

-- Coq line 616: Lemma subst_ee_open_ee_var
theorem subst_ee_open_ee_var : ∀ x y u e, y ≠ x → def_term u →
  open_ee (subst_ee x u e) (trm_fvar y) = subst_ee x u (open_ee e (trm_fvar y)) := by
  sorry

-- Coq line 626: Lemma subst_ee_intro
theorem subst_ee_intro : ∀ x u e,
  x ∉ fv_ee e → def_term u →
  open_ee e u = subst_ee x u (e open_ee_var x) := by
  sorry -- Need subst_ee_open_ee first

-- Coq line 637: Lemma subst_te_open_ee_var
theorem subst_te_open_ee_var : ∀ Z P x e,
  open_ee (subst_te Z P e) (trm_fvar x) = subst_te Z P (open_ee e (trm_fvar x)) := by
  intro Z P x
  simp only [open_ee]
  -- Need to prove the general version with open_ee_rec
  intro e
  suffices h : ∀ k, open_ee_rec k (trm_fvar x) (subst_te Z P e) = 
                     subst_te Z P (open_ee_rec k (trm_fvar x) e) by
    exact h 0
  intro k
  induction e generalizing k with
  | trm_bvar n =>
    simp [open_ee_rec, subst_te]
    split_ifs <;> rfl
  | trm_fvar y =>
    simp [open_ee_rec, subst_te]
  | trm_abs V e1 ih =>
    simp only [open_ee_rec, subst_te]
    congr 1
    exact ih (k + 1)
  | trm_app e1 e2 ih1 ih2 =>
    simp [open_ee_rec, subst_te, ih1, ih2]
  | trm_tabs V e1 ih =>
    simp [open_ee_rec, subst_te, ih]
  | trm_tapp e1 V ih =>
    simp [open_ee_rec, subst_te, ih]

-- Coq line 647: Lemma subst_ee_open_te_var
theorem subst_ee_open_te_var : ∀ z u e X, def_term u →
  open_te (subst_ee z u e) (typ_fvar X) = subst_ee z u (open_te e (typ_fvar X)) := by
  sorry -- Need to handle type substitution in substituted terms

-- Substitutions preserve local closure

-- Coq line 657: Lemma subst_tt_type
theorem subst_tt_type : ∀ T Z P,
  def_type T → def_type P → def_type (subst_tt Z P T) := by
  sorry -- Complex proof with substitution under binders

-- Coq line 665: Lemma subst_te_term
theorem subst_te_term : ∀ e Z P,
  def_term e → def_type P → def_term (subst_te Z P e) := by
  sorry -- Complex proof with substitution under binders

-- Coq line 673: Lemma subst_ee_term
theorem subst_ee_term : ∀ e1 Z e2,
  def_term e1 → def_term e2 → def_term (subst_ee Z e2 e1) := by
  sorry -- Complex proof with substitution under binders

-- Properties of well-formedness of a type in an environment

-- Coq line 690: Lemma wft_type
theorem wft_type : ∀ E T,
  wft E T → def_type T := by
  intro E T H
  induction H with
  | wft_top E => exact def_type.type_top
  | wft_var U E X Hbind => exact def_type.type_var X
  | wft_arrow E T1 T2 H1 H2 ih1 ih2 => exact def_type.type_arrow T1 T2 ih1 ih2
  | wft_all L E T1 T2 H1 H2 ih1 ih2 =>
    apply def_type.type_all L T1 T2
    · exact ih1
    · intro X HX
      exact ih2 X HX

-- Coq line 698: Lemma wft_weaken
theorem wft_weaken : ∀ G T E F,
  wft (E ++ G) T →
  ok (E ++ F ++ G) →
  wft (E ++ F ++ G) T := by
  sorry

-- Coq line 713: Lemma wft_narrow
theorem wft_narrow : ∀ V F U T E X,
  wft (E ++ [(X, bind_sub V)] ++ F) T →
  ok (E ++ [(X, bind_sub U)] ++ F) →
  wft (E ++ [(X, bind_sub U)] ++ F) T := by
  sorry

-- Coq line 730: Lemma wft_strengthen
theorem wft_strengthen : ∀ E F x U T,
  wft (E ++ [(x, bind_typ U)] ++ F) T → wft (E ++ F) T := by
  sorry

-- Coq line 747: Lemma wft_subst_tb
theorem wft_subst_tb : ∀ F Q E Z P T,
  wft (E ++ [(Z, bind_sub Q)] ++ F) T →
  wft E P →
  ok (E ++ map_subst_tb Z P F) →
  wft (E ++ map_subst_tb Z P F) (subst_tt Z P T) := by
  sorry

-- Coq line 773: Lemma wft_open
theorem wft_open : ∀ E U T1 T2,
  ok E →
  wft E (typ_all T1 T2) →
  wft E U →
  wft E (open_tt T2 U) := by
  sorry

-- Relations between well-formed environment and types well-formed in environments

-- Coq line 795: Lemma ok_from_okt
theorem ok_from_okt : ∀ E,
  okt E → ok E := by
  sorry -- This depends on the axiomatized ok predicate

-- Coq line 805: Lemma wft_from_env_has_sub
theorem wft_from_env_has_sub : ∀ x U E,
  okt E → binds x (bind_sub U) E → wft E U := by
  sorry -- Requires weakening lemma

-- Coq line 824: Lemma wft_from_env_has_typ
theorem wft_from_env_has_typ : ∀ x U E,
  okt E → binds x (bind_typ U) E → wft E U := by
  sorry -- Requires weakening lemma

-- Coq line 843: Lemma wft_from_okt_typ
theorem wft_from_okt_typ : ∀ x T E,
  okt ((x, bind_typ T) :: E) → wft E T := by
  sorry -- Depends on okt_push_typ_inv which is defined below

-- Coq line 852: Lemma wft_from_okt_sub
theorem wft_from_okt_sub : ∀ x T E,
  okt ((x, bind_sub T) :: E) → wft E T := by
  sorry -- Depends on okt_push_sub_inv which is defined below

-- Coq line 863: Lemma wft_weaken_right
theorem wft_weaken_right : ∀ T E F,
  wft E T →
  ok (E ++ F) →
  wft (E ++ F) T := by
  sorry -- Need to handle the argument order for wft_weaken

-- Properties of well-formedness of an environment

-- Coq line 882: Lemma okt_push_inv
theorem okt_push_inv : ∀ E X B,
  okt ((X, B) :: E) → ∃ T, B = bind_sub T ∨ B = bind_typ T := by
  intro E X B H
  cases H with
  | okt_sub E' X' T' _ _ _ => 
    use T'; left; rfl
  | okt_typ E' x' T' _ _ _ => 
    use T'; right; rfl

-- Coq line 891: Lemma okt_push_sub_inv
theorem okt_push_sub_inv : ∀ E X T,
  okt ((X, bind_sub T) :: E) → okt E ∧ wft E T ∧ E.lookup X = none := by
  intro E X T H
  cases H with
  | okt_sub _ _ _ HE HT Hfresh => exact ⟨HE, HT, Hfresh⟩

-- Coq line 900: Lemma okt_push_sub_type
theorem okt_push_sub_type : ∀ E X T,
  okt ((X, bind_sub T) :: E) → def_type T := by
  intro E X T H
  obtain ⟨_, HT, _⟩ := okt_push_sub_inv E X T H
  exact wft_type E T HT

-- Coq line 904: Lemma okt_push_typ_inv
theorem okt_push_typ_inv : ∀ E x T,
  okt ((x, bind_typ T) :: E) → okt E ∧ wft E T ∧ E.lookup x = none := by
  intro E x T H
  cases H with
  | okt_typ _ _ _ HE HT Hfresh => exact ⟨HE, HT, Hfresh⟩

-- Coq line 913: Lemma okt_push_typ_type
theorem okt_push_typ_type : ∀ E X T,
  okt ((X, bind_typ T) :: E) → def_type T := by
  intro E X T H
  obtain ⟨_, HT, _⟩ := okt_push_typ_inv E X T H
  exact wft_type E T HT

-- Now we can implement wft_from_okt lemmas that were declared with sorry above
theorem wft_from_okt_typ.impl : ∀ x T E,
  okt ((x, bind_typ T) :: E) → wft E T := by
  intro x T E H
  obtain ⟨_, HT, _⟩ := okt_push_typ_inv E x T H
  exact HT

theorem wft_from_okt_sub.impl : ∀ x T E,
  okt ((x, bind_sub T) :: E) → wft E T := by
  intro x T E H
  obtain ⟨_, HT, _⟩ := okt_push_sub_inv E x T H
  exact HT

-- Coq line 921: Lemma okt_narrow
theorem okt_narrow : ∀ V E F U X,
  okt (E ++ [(X, bind_sub V)] ++ F) →
  wft E U →
  okt (E ++ [(X, bind_sub U)] ++ F) := by
  sorry

-- Coq line 938: Lemma okt_strengthen
theorem okt_strengthen : ∀ x T E F,
  okt (E ++ [(x, bind_typ T)] ++ F) →
  okt (E ++ F) := by
  sorry

-- Coq line 954: Lemma okt_subst_tb
theorem okt_subst_tb : ∀ Q Z P E F,
  okt (E ++ [(Z, bind_sub Q)] ++ F) →
  wft E P →
  okt (E ++ map_subst_tb Z P F) := by
  sorry

-- Environment is unchanged by substitution from a fresh name

-- Coq line 979: Lemma notin_fv_tt_open
theorem notin_fv_tt_open : ∀ Y X T,
  X ∉ fv_tt (T open_tt_var Y) →
  X ∉ fv_tt T := by
  sorry -- Requires induction on T structure

-- Coq line 989: Lemma notin_fv_wf
theorem notin_fv_wf : ∀ E X T,
  wft E T → X ∉ dom E → X ∉ fv_tt T := by
  sorry

-- Coq line 999: Lemma map_subst_tb_id
theorem map_subst_tb_id : ∀ G Z P,
  okt G → Z ∉ dom G → G = map_subst_tb Z P G := by
  sorry -- Requires notin_fv_wf and subst_tt_fresh

-- Regularity of relations

-- Coq line 1014: Lemma sub_regular
theorem sub_regular : ∀ E S T,
  sub E S T → okt E ∧ wft E S ∧ wft E T := by
  sorry

-- Coq line 1025: Lemma typing_regular
theorem typing_regular : ∀ E e T,
  typing E e T → okt E ∧ def_term e ∧ wft E T := by
  sorry

-- Coq line 1062: Lemma value_regular
theorem value_regular : ∀ t,
  value t → def_term t := by
  intro t Hval
  cases Hval with
  | value_abs V e1 Hterm => exact Hterm
  | value_tabs V e1 Hterm => exact Hterm

-- Coq line 1070: Lemma red_regular
theorem red_regular : ∀ t t',
  red t t' → def_term t ∧ def_term t' := by
  intro t t' Hred
  induction Hred with
  | red_app_1 e1 e1' e2 He2 _ ih =>
    obtain ⟨H1, H2⟩ := ih
    exact ⟨def_term.term_app _ _ H1 He2, def_term.term_app _ _ H2 He2⟩
  | red_app_2 e1 e2 e2' Hval _ ih =>
    obtain ⟨H1, H2⟩ := ih
    have He1 := value_regular _ Hval
    exact ⟨def_term.term_app _ _ He1 H1, def_term.term_app _ _ He1 H2⟩
  | red_tapp e1 e1' V HV _ ih =>
    obtain ⟨H1, H2⟩ := ih
    exact ⟨def_term.term_tapp _ _ H1 HV, def_term.term_tapp _ _ H2 HV⟩
  | red_abs V e1 v2 Hterm Hval =>
    have Hv2 := value_regular _ Hval
    constructor
    · exact def_term.term_app _ _ Hterm Hv2
    · sorry -- Need subst_ee_term: open_ee e1 v2 = subst_ee x v2 (e1 open_ee_var x) for fresh x
  | red_tabs V1 e1 V2 Hterm HV =>
    constructor
    · exact def_term.term_tapp _ _ Hterm HV
    · sorry -- Need subst_te_term: open_te e1 V2 = subst_te X V2 (e1 open_te_var X) for fresh X

-- Properties of Subtyping

-- Coq line 1122: Lemma sub_reflexivity
theorem sub_reflexivity : ∀ E T,
  okt E →
  wft E T →
  sub E T T := by
  sorry -- Requires careful induction on wft structure

-- Coq line 1135: Lemma sub_weakening
theorem sub_weakening : ∀ E F G S T,
  sub (E ++ G) S T →
  okt (E ++ F ++ G) →
  sub (E ++ F ++ G) S T := by
  sorry

-- Narrowing and transitivity

-- Coq line 1159: Lemma sub_narrowing_aux
theorem sub_narrowing_aux : ∀ Q F E Z P S T,
  (∀ E S T, sub E S Q → sub E Q T → sub E S T) →
  sub (E ++ [(Z, bind_sub Q)] ++ F) S T →
  sub E P Q →
  sub (E ++ [(Z, bind_sub P)] ++ F) S T := by
  sorry

-- Coq line 1183: Lemma sub_transitivity
theorem sub_transitivity : ∀ Q E S T,
  sub E S Q → sub E Q T → sub E S T := by
  sorry

-- Coq line 1203: Lemma sub_narrowing
theorem sub_narrowing : ∀ Q E F Z P S T,
  sub E P Q →
  sub (E ++ [(Z, bind_sub Q)] ++ F) S T →
  sub (E ++ [(Z, bind_sub P)] ++ F) S T := by
  sorry

-- Coq line 1218: Lemma sub_through_subst_tt
theorem sub_through_subst_tt : ∀ Q E F Z S T P,
  sub (E ++ [(Z, bind_sub Q)] ++ F) S T →
  sub E P Q →
  sub (E ++ map_subst_tb Z P F) (subst_tt Z P S) (subst_tt Z P T) := by
  sorry

-- Properties of Typing

-- Coq line 1254: Lemma typing_weakening
theorem typing_weakening : ∀ E F G e T,
  typing (E ++ G) e T →
  okt (E ++ F ++ G) →
  typing (E ++ F ++ G) e T := by
  sorry

-- Coq line 1273: Lemma sub_strengthening
theorem sub_strengthening : ∀ x U E F S T,
  sub (E ++ [(x, bind_typ U)] ++ F) S T →
  sub (E ++ F) S T := by
  sorry

-- Coq line 1288: Lemma typing_narrowing
theorem typing_narrowing : ∀ Q E F X P e T,
  sub E P Q →
  typing (E ++ [(X, bind_sub Q)] ++ F) e T →
  typing (E ++ [(X, bind_sub P)] ++ F) e T := by
  sorry

-- Coq line 1306: Lemma typing_through_subst_ee
theorem typing_through_subst_ee : ∀ U E F x T e u,
  typing (E ++ [(x, bind_typ U)] ++ F) e T →
  typing E u U →
  typing (E ++ F) (subst_ee x u e) T := by
  sorry

-- Coq line 1329: Lemma typing_through_subst_te
theorem typing_through_subst_te : ∀ Q E F Z e T P,
  typing (E ++ [(Z, bind_sub Q)] ++ F) e T →
  sub E P Q →
  typing (E ++ map_subst_tb Z P F) (subst_te Z P e) (subst_tt Z P T) := by
  sorry

-- Preservation

-- Coq line 1359: Lemma typing_inv_abs
theorem typing_inv_abs : ∀ E S1 e1 T,
  typing E (trm_abs S1 e1) T →
  ∀ U1 U2, sub E T (typ_arrow U1 U2) →
     sub E U1 S1
  ∧ ∃ S2, ∃ L : Finset Var, ∀ x, x ∉ L →
     typing ((x, bind_typ S1) :: E) (open_ee e1 (trm_fvar x)) S2 ∧ sub E S2 U2 := by
  sorry

-- Coq line 1371: Lemma typing_inv_tabs
theorem typing_inv_tabs : ∀ E S1 e1 T,
  typing E (trm_tabs S1 e1) T →
  ∀ U1 U2, sub E T (typ_all U1 U2) →
     sub E U1 S1
  ∧ ∃ S2, ∃ L : Finset Var, ∀ X, X ∉ L →
     typing ((X, bind_sub U1) :: E) (open_te e1 (typ_fvar X)) (open_tt S2 (typ_fvar X))
     ∧ sub ((X, bind_sub U1) :: E) (open_tt S2 (typ_fvar X)) (open_tt U2 (typ_fvar X)) := by
  sorry

-- Coq line 1391: Lemma preservation_result
theorem preservation_result : preservation := by
  sorry

-- Progress

-- Coq line 1426: Lemma canonical_form_abs
theorem canonical_form_abs : ∀ t U1 U2,
  value t → typing [] t (typ_arrow U1 U2) →
  ∃ V e1, t = trm_abs V e1 := by
  intro t U1 U2 Hval Htyp
  cases Hval with
  | value_abs V e1 _ => exact ⟨V, e1, rfl⟩
  | value_tabs V e1 Hterm => 
    -- Show tabs cannot have arrow type
    -- We need to analyze the typing derivation
    exfalso
    sorry -- Need typing inversion lemma

-- Coq line 1439: Lemma canonical_form_tabs
theorem canonical_form_tabs : ∀ t U1 U2,
  value t → typing [] t (typ_all U1 U2) →
  ∃ V e1, t = trm_tabs V e1 := by
  intro t U1 U2 Hval Htyp
  cases Hval with
  | value_abs V e1 Hterm => 
    -- Show abs cannot have forall type
    exfalso
    sorry -- Need typing inversion lemma
  | value_tabs V e1 _ => exact ⟨V, e1, rfl⟩

-- Coq line 1455: Lemma progress_result
theorem progress_result : progress := by
  sorry

end Lp2lc.Active
