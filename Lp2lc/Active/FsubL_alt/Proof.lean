-- Proof scaffolds for System-F with Subtyping, Bottom and Lower Bounds
import Lp2lc.Active.FsubL_alt.Def

namespace Lp2lc.Active.FsubL_alt

-- Line 464: Substitution on indices is identity on well-formed terms
theorem open_tt_rec_type_core : ∀ T j V U i, i ≠ j →
  (open_tt_rec j V T) = open_tt_rec i U (open_tt_rec j V T) →
  T = open_tt_rec i U T := by
  sorry

-- Line 472: Well-formed types are identity under opening
theorem open_tt_rec_type : ∀ T U,
  type T → ∀ k, T = open_tt_rec k U T := by
  sorry

-- Line 481: Substitution for a fresh name is identity
theorem subst_tt_fresh : ∀ Z U T,
  Z ∉ fv_tt T → subst_tt Z U T = T := by
  sorry

-- Line 490: Substitution distributes on the open operation
theorem subst_tt_open_tt_rec : ∀ T1 T2 X P n, type P →
  subst_tt X P (open_tt_rec n T2 T1) =
  open_tt_rec n (subst_tt X P T2) (subst_tt X P T1) := by
  sorry

-- Line 500: Substitution distributes on open_tt
theorem subst_tt_open_tt : ∀ T1 T2 X P, type P →
  subst_tt X P (open_tt T1 T2) =
  open_tt (subst_tt X P T1) (subst_tt X P T2) := by
  sorry

-- Line 509: Substitution and open_var for distinct names commute
theorem subst_tt_open_tt_var : ∀ X Y U T, Y ≠ X → type U →
  ((subst_tt X U T) open_tt_var Y) = subst_tt X U (T open_tt_var Y) := by
  sorry

-- Line 519: Opening with substitution introduction
theorem subst_tt_intro : ∀ X T2 U,
  X ∉ fv_tt T2 → type U →
  open_tt T2 U = subst_tt X U (T2 open_tt_var X) := by
  sorry

-- Line 531: Term core lemma for type opening
theorem open_te_rec_term_core : ∀ e j u i P,
  open_ee_rec j u e = open_te_rec i P (open_ee_rec j u e) →
  e = open_te_rec i P e := by
  sorry

-- Line 538: Type opening core lemma for terms
theorem open_te_rec_type_core : ∀ e j Q i P, i ≠ j →
  open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) →
  e = open_te_rec i P e := by
  sorry

-- Line 547: Well-formed terms are identity under type opening
theorem open_te_rec_term : ∀ e U,
  term e → ∀ k, e = open_te_rec k U e := by
  sorry

-- Line 560: Type substitution with fresh name in terms
theorem subst_te_fresh : ∀ X U e,
  X ∉ fv_te e → subst_te X U e = e := by
  sorry

-- Line 568: Type substitution distributes on term type opening
theorem subst_te_open_te : ∀ e T X U, type U →
  subst_te X U (open_te e T) =
  open_te (subst_te X U e) (subst_tt X U T) := by
  sorry

-- Line 579: Type substitution and open_var commute
theorem subst_te_open_te_var : ∀ X Y U e, Y ≠ X → type U →
  ((subst_te X U e) open_te_var Y) = subst_te X U (e open_te_var Y) := by
  sorry

-- Line 589: Type substitution introduction for terms
theorem subst_te_intro : ∀ X U e,
  X ∉ fv_te e → type U →
  open_te e U = subst_te X U (e open_te_var X) := by
  sorry

-- Line 601: Term substitution core lemma
theorem open_ee_rec_term_core : ∀ e j v u i, i ≠ j →
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) →
  e = open_ee_rec i u e := by
  sorry

-- Line 609: Type-term opening core lemma
theorem open_ee_rec_type_core : ∀ e j V u i,
  open_te_rec j V e = open_ee_rec i u (open_te_rec j V e) →
  e = open_ee_rec i u e := by
  sorry

-- Line 616: Well-formed terms are identity under term opening
theorem open_ee_rec_term : ∀ u e,
  term e → ∀ k, e = open_ee_rec k u e := by
  sorry

-- Line 628: Term substitution with fresh name
theorem subst_ee_fresh : ∀ x u e,
  x ∉ fv_ee e → subst_ee x u e = e := by
  sorry

-- Line 637: Term substitution distributes on opening
theorem subst_ee_open_ee : ∀ t1 t2 u x, term u →
  subst_ee x u (open_ee t1 t2) =
  open_ee (subst_ee x u t1) (subst_ee x u t2) := by
  sorry

-- Line 649: Term substitution and open_var commute
theorem subst_ee_open_ee_var : ∀ x y u e, y ≠ x → term u →
  ((subst_ee x u e) open_ee_var y) = subst_ee x u (e open_ee_var y) := by
  sorry

-- Line 659: Term substitution introduction
theorem subst_ee_intro : ∀ x u e,
  x ∉ fv_ee e → term u →
  open_ee e u = subst_ee x u (e open_ee_var x) := by
  sorry

-- Line 670: Type substitution and term opening commute
theorem subst_te_open_ee_var : ∀ Z P x e,
  ((subst_te Z P e) open_ee_var x) = subst_te Z P (e open_ee_var x) := by
  sorry

-- Line 680: Term substitution and type opening commute
theorem subst_ee_open_te_var : ∀ z u e X, term u →
  ((subst_ee z u e) open_te_var X) = subst_ee z u (e open_te_var X) := by
  sorry

-- Line 690: Type substitution preserves type closure
theorem subst_tt_type : ∀ T Z P,
  type T → type P → type (subst_tt Z P T) := by
  sorry

-- Line 698: Type substitution preserves term closure
theorem subst_te_term : ∀ e Z P,
  term e → type P → term (subst_te Z P e) := by
  sorry

-- Line 706: Term substitution preserves term closure
theorem subst_ee_term : ∀ e1 Z e2,
  term e1 → term e2 → term (subst_ee Z e2 e1) := by
  sorry

-- Line 723: Well-formed types are locally closed
theorem wft_type : ∀ E T,
  wft E T → type T := by
  sorry

-- Line 828: Well-formedness through opening
theorem wft_open : ∀ E U T0 T1 T2,
  okt E →
  wft E (Typ.typ_all T0 T1 T2) →
  wft E U →
  wft E (open_tt T2 U) := by
  sorry

-- Line 857: Extract well-formedness from subtyping environment
theorem wft_from_env_has_sub : ∀ x U0 U1 E,
  okt E → binds x (Bind.bind_sub U0 U1) E → wft E U0 ∧ wft E U1 := by
  sorry

-- Line 876: Extract well-formedness from typing environment
theorem wft_from_env_has_typ : ∀ x U E,
  okt E → binds x (Bind.bind_typ U) E → wft E U := by
  sorry

-- Line 895: Extract well-formedness from typing environment head
theorem wft_from_okt_typ : ∀ x T E,
  okt (Env.push E (x, Bind.bind_typ T)) → wft E T := by
  sorry

-- Line 904: Extract well-formedness from subtyping environment head
theorem wft_from_okt_sub : ∀ x T0 T1 E,
  okt (Env.push E (x, Bind.bind_sub T0 T1)) → wft E T0 ∧ wft E T1 := by
  sorry

-- Line 934: Environment inversion
theorem okt_push_inv : ∀ E X B,
  okt (Env.push E (X, B)) → ∃ T0 T1, B = Bind.bind_sub T0 T1 ∨ ∃ T, B = Bind.bind_typ T := by
  sorry

-- Line 943: Subtyping environment inversion
theorem okt_push_sub_inv : ∀ E X T0 T1,
  okt (Env.push E (X, Bind.bind_sub T0 T1)) → okt E ∧ wft E T0 ∧ wft E T1 ∧ X ∉ Env.dom E := by
  sorry

-- Line 952: Extract type from subtyping environment
theorem okt_push_sub_type : ∀ E X T0 T1,
  okt (Env.push E (X, Bind.bind_sub T0 T1)) → type T0 ∧ type T1 := by
  sorry

-- Line 956: Typing environment inversion
theorem okt_push_typ_inv : ∀ E x T,
  okt (Env.push E (x, Bind.bind_typ T)) → okt E ∧ wft E T ∧ x ∉ Env.dom E := by
  sorry

-- Line 965: Extract type from typing environment
theorem okt_push_typ_type : ∀ E X T,
  okt (Env.push E (X, Bind.bind_typ T)) → type T := by
  sorry

-- Line 1041: Fresh variables and opening
theorem notin_fv_tt_open : ∀ Y X T,
  X ∉ fv_tt (T open_tt_var Y) →
  X ∉ fv_tt T := by
  sorry

-- Line 1051: Fresh variables in well-formed types
theorem notin_fv_wf : ∀ E X T,
  wft E T → X ∉ Env.dom E → X ∉ fv_tt T := by
  sorry

-- Line 1079: Subtyping regularity
theorem sub_regular : ∀ E S T,
  sub E S T → okt E ∧ wft E S ∧ wft E T := by
  sorry

-- Line 1098: Typing regularity
theorem typing_regular : ∀ E e T,
  typing E e T → okt E ∧ term e ∧ wft E T := by
  sorry

-- Line 1141: Value regularity
theorem value_regular : ∀ t,
  value t → term t := by
  sorry

-- Line 1149: Reduction regularity
theorem red_regular : ∀ t t',
  red t t' → term t ∧ term t' := by
  sorry

-- Line 1201: Subtyping reflexivity
theorem sub_reflexivity : ∀ E T,
  okt E →
  wft E T →
  sub E T T := by
  sorry

-- Line 1294: Subtyping narrowing from empty
theorem sub_narrowing_empty : ∀ Q0 Q1 Z P0 P1 S T,
  sub (∅ : Env) P0 Q0 → sub (∅ : Env) Q1 P1 →
  sub (Env.push (∅ : Env) (Z, Bind.bind_sub Q0 Q1)) S T →
  sub (Env.push (∅ : Env) (Z, Bind.bind_sub P0 P1)) S T := by
  sorry

-- Line 1432: Typing narrowing from empty
theorem typing_narrowing_empty : ∀ Q0 Q1 X P0 P1 e T,
  sub (∅ : Env) P0 Q0 → sub (∅ : Env) Q1 P1 →
  typing (Env.push (∅ : Env) (X, Bind.bind_sub Q0 Q1)) e T →
  typing (Env.push (∅ : Env) (X, Bind.bind_sub P0 P1)) e T := by
  sorry

-- Line 1527: Possible types for values  
theorem possible_types_value : ∀ p T,
  value p → typing (∅ : Env) p T → ∃ S, typing (∅ : Env) p S ∧ sub (∅ : Env) S T := by
  sorry

-- Line 1540: Possible types closure
theorem possible_types_closure : ∀ v T U,
  value v → typing (∅ : Env) v T → sub (∅ : Env) T U → typing (∅ : Env) v U := by
  sorry

-- Line 1560: Possible types and typing
theorem possible_types_typing : ∀ v T,
  value v → typing (∅ : Env) v T → 
  (T = Typ.typ_bot ∨ ∃ S, sub (∅ : Env) S T ∧ typing (∅ : Env) v S ∧ S ≠ Typ.typ_bot) := by
  sorry

-- Line 1587: Typing inversion for abstraction
theorem typing_inv_abs : ∀ S1 e1 T,
  typing (∅ : Env) (Trm.trm_abs S1 e1) T →
  ∀ U1 U2, sub (∅ : Env) T (Typ.typ_arrow U1 U2) →
  sub (∅ : Env) U1 S1 ∧
  ∃ (S2 : Typ) (L : Vars), ∀ x, x ∉ L →
    typing (Env.push (∅ : Env) (x, Bind.bind_typ S1)) (e1 open_ee_var x) S2 ∧ sub (∅ : Env) S2 U2 := by
  sorry

-- Line 1603: Typing inversion for type abstraction
theorem typing_inv_tabs : ∀ S10 S11 e1 T,
  typing (∅ : Env) (Trm.trm_tabs S10 S11 e1) T →
  ∀ U0 U1 U2, sub (∅ : Env) T (Typ.typ_all U0 U1 U2) →
  sub (∅ : Env) U0 S10 ∧ sub (∅ : Env) S11 U1 ∧
  ∃ (S2 : Typ) (L : Vars), ∀ X, X ∉ L →
    typing (Env.push (∅ : Env) (X, Bind.bind_sub U0 U1)) (e1 open_te_var X) (S2 open_tt_var X) ∧
    sub (Env.push (∅ : Env) (X, Bind.bind_sub U0 U1)) (S2 open_tt_var X) (U2 open_tt_var X) := by
  sorry

-- Line 1624: Preservation theorem
theorem preservation_result : preservation := by
  sorry

-- Line 1660: Values cannot have bottom type
theorem value_not_bot : ∀ t T,
  value t → typing (∅ : Env) t T → T ≠ Typ.typ_bot := by
  sorry

-- Line 1668: Canonical form for abstraction
theorem canonical_form_abs : ∀ t U1 U2,
  value t → typing (∅ : Env) t (Typ.typ_arrow U1 U2) →
  ∃ V e1, t = Trm.trm_abs V e1 := by
  sorry

-- Line 1678: Canonical form for type abstraction  
theorem canonical_form_tabs : ∀ t U0 U1 U2,
  value t → typing (∅ : Env) t (Typ.typ_all U0 U1 U2) →
  ∃ V0 V1 e1, t = Trm.trm_tabs V0 V1 e1 := by
  sorry

-- Line 1691: Progress theorem
theorem progress_result : progress := by
  sorry

end Lp2lc.Active.FsubL_alt
