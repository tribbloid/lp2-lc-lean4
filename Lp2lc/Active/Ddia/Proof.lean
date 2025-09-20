/-****************************************************************************
* Ddia (DOT-style calculus) – Theorems (scaffold)
* All proofs are `sorry` placeholders per 1_Scaffold.md; no axioms introduced.
*****************************************************************************-/

import Aesop
import Mathlib.Data.Finset.Basic
import «Lp2lc».Active.Ddia.Def
import «Lp2lc».Active.Ddia.Auxiliary

namespace Lp2lc.Active.Ddia

open typ trm def_type def_term wft wfe value sub has typing red

/- Selection of core lemmas stubbed to establish structure. The full list
   is tracked in Proof.progress.md and will be added incrementally. -/


-- A few substitution lemmas
-- We discharge subst_t_type and subst_e_term mutually, relying on distribution lemmas in Auxiliary.lean.
-- A few substitution lemmas (stubs)
-- Coq line 574: Lemma subst_e_term
-- Substitution over terms preserves local closure of terms.
theorem subst_e_term : ∀ {e1 z e2}, def_term e1 → def_term e2 → def_term (subst_e z e2 e1) := by
  -- TODO: mutual induction over terms
  intro _ _ _ _ _; sorry

-- Coq line 568: Lemma subst_t_type (adapted to Ddia: subst over types uses terms)
-- Substitution over types preserves local closure of types.
theorem subst_t_type : ∀ {T z u}, def_type T → def_term u → def_type (subst_t z u T) := by
  -- TODO: mutual induction over types/terms
  intro _ _ _ _ _; sorry

/- Section: Properties of Substitutions (Opening, Substitution, Local Closure) -/
-- Opening and substitution infrastructure (typed)
-- Core open_rec lemma (type part)
theorem open_rec_lc_core_t : ∀ (T : typ) (j : Nat) (v u : trm) (i : Nat),
  i ≠ j → open_t_rec j v T = open_t_rec i u (open_t_rec j v T) → T = open_t_rec i u T := by
  sorry

-- Core open_rec lemma (term part)
theorem open_rec_lc_core_e : ∀ (e : trm) (j : Nat) (v u : trm) (i : Nat),
  i ≠ j → open_e_rec j v e = open_e_rec i u (open_e_rec j v e) → e = open_e_rec i u e := by
  sorry

-- Opening preserves equality for locally closed objects
theorem open_rec_lc_t : ∀ (T : typ), def_type T → ∀ (u : trm) (k : Nat), T = open_t_rec k u T := by
  sorry

theorem open_rec_lc_e : ∀ (e : trm), def_term e → ∀ (u : trm) (k : Nat), e = open_e_rec k u e := by
  sorry

-- Opening with a fresh variable does nothing on types
theorem open_t_var_type : ∀ (x : Var) (T : typ), def_type T → open_t T (trm_fvar x) = T := by
  sorry

-- Substitution for a fresh name is identity

theorem subst_fresh_t : ∀ (T : typ) (z : Var) (u : trm), z ∉ fv_t T → subst_t z u T = T := by
  sorry

theorem subst_fresh_e : ∀ (e : trm) (z : Var) (u : trm), z ∉ fv_e e → subst_e z u e = e := by
  sorry

-- Substitution distributes over open_rec

theorem subst_open_rec_t : ∀ (T1 : typ) (t2 : trm) (x : Var) (u : trm) (n : Nat), def_term u →
  subst_t x u (open_t_rec n t2 T1) = open_t_rec n (subst_e x u t2) (subst_t x u T1) := by
  sorry

theorem subst_open_rec_e : ∀ (t1 t2 : trm) (x : Var) (u : trm) (n : Nat), def_term u →
  subst_e x u (open_e_rec n t2 t1) = open_e_rec n (subst_e x u t2) (subst_e x u t1) := by
  sorry

-- Substitution distributes over open (wrappers)

theorem subst_t_open_t : ∀ (T1 : typ) (t2 : trm) (x : Var) (u : trm), def_term u →
  subst_t x u (open_t T1 t2) = open_t (subst_t x u T1) (subst_e x u t2) := by
  sorry

theorem subst_e_open_e : ∀ (t1 t2 : trm) (x : Var) (u : trm), def_term u →
  subst_e x u (open_e t1 t2) = open_e (subst_e x u t1) (subst_e x u t2) := by
  sorry

-- Substitution and open_var commute when names are distinct

theorem subst_t_open_t_var : ∀ (x y : Var) (u : trm) (T : typ), y ≠ x → def_term u →
  open_t (subst_t x u T) (trm_fvar y) = subst_t x u (open_t T (trm_fvar y)) := by
  sorry

theorem subst_e_open_e_var : ∀ (x y : Var) (u : trm) (e : trm), y ≠ x → def_term u →
  open_e (subst_e x u e) (trm_fvar y) = subst_e x u (open_e e (trm_fvar y)) := by
  sorry

-- Substitution intro lemmas

theorem subst_t_intro : ∀ (x : Var) (T2 : typ) (u : trm), x ∉ fv_t T2 → def_term u →
  open_t T2 u = subst_t x u (open_t T2 (trm_fvar x)) := by
  sorry

theorem subst_e_intro : ∀ (x : Var) (t2 : trm) (u : trm), x ∉ fv_e t2 → def_term u →
  open_e t2 u = subst_e x u (open_e t2 (trm_fvar x)) := by
  sorry

-- Substitutions preserve local closure

theorem subst_lc_t : ∀ (T : typ), def_type T → ∀ (z : Var) (u : trm), def_term u → def_type (subst_t z u T) := by
  sorry

theorem subst_lc_e : ∀ (e : trm), def_term e → ∀ (z : Var) (u : trm), def_term u → def_term (subst_e z u e) := by
  sorry

/- Section: Regularity (terms, typing, reduction) -/
-- Coq line 596: Lemma value_is_term
theorem value_is_term : ∀ e, value e → def_term e := by
  intro e h; cases h <;> aesop

-- Coq line 614: Lemma wft_type
theorem wft_type : ∀ {E T}, wft E T → def_type T := by
  -- TODO: will be proved using mutual recursion with wfe_term and regularity lemmas
  intro _ _ _; sorry

-- Coq line 1024: Lemma typing_regular
theorem typing_regular : ∀ {E e T}, typing E e T → okt E ∧ wfe E e ∧ wft E T := by
  -- TODO: structural cases on typing
  sorry

-- Coq line 608: wf_lc (mutual regularity)
theorem wf_lc :
  (∀ {E T}, wft E T → def_type T) ∧
  (∀ {E e}, wfe E e → def_term e) := by
  sorry

-- Coq line 620: wfe_term (projection of wf_lc)
theorem wfe_term : ∀ {E e}, wfe E e → def_term e := by
  intro E e h; -- will use wf_lc in the real proof
  sorry

-- Coq line 814: ok_from_okt
-- Bridge from well-formed environment to abstract ok predicate from Shared
-- (the actual proof will follow the project’s environment invariants)
theorem ok_from_okt : ∀ {E}, okt E → ok E := by
  intro E _; sorry

-- Coq line 1049: value_regular (alias of value_is_term)
theorem value_regular : ∀ t, value t → def_term t := by
  intro t h; exact value_is_term t h

-- Coq line 1057: red_regular (terms preserved by one-step reduction)
theorem red_regular : ∀ t t', red t t' → def_term t ∧ def_term t' := by
  intro _ _ _; sorry

-- Coq line 1815: value_red_contra
theorem value_red_contra : ∀ {e e'}, value e → red e e' → False := by
  intro e e' hv hr; sorry

/- Properties of Subtyping -/
-- Coq 1116: sub_reflexivity
theorem sub_reflexivity : ∀ {E T}, okt E → wft E T → sub E T T := by
  intro E T hOk hW; 
  -- TODO: structural induction over hW, cofinite in all-case
  sorry

/- Weakening, narrowing, substitution for sub/has and typing -/
-- Coq lines ~1132: sub_has_weakening (pair)
theorem sub_has_weakening :
  (∀ {E0 S T}, sub E0 S T → ∀ {E F G}, E0 = E ++ G → okt (E ++ F ++ G) → sub (E ++ F ++ G) S T) ∧
  (∀ {E0 p T}, has E0 p T → ∀ {E F G}, E0 = E ++ G → okt (E ++ F ++ G) → has (E ++ F ++ G) p T) := by
  sorry

-- Coq 1158: sub_weakening
 theorem sub_weakening : ∀ {E F G S T}, sub (E ++ G) S T → okt (E ++ F ++ G) → sub (E ++ F ++ G) S T := by
  sorry

-- Coq 1166: sub_weakening1
 theorem sub_weakening1 : ∀ {E F G S T}, sub E S T → okt (E ++ F ++ G) → sub (E ++ F ++ G) S T := by
  sorry

-- Coq 1181: sub_weakening_empty
 theorem sub_weakening_empty : ∀ {E S T}, sub [] S T → okt E → sub E S T := by
  sorry

-- Coq 1196: has_weakening
 theorem has_weakening : ∀ {E F G p T}, has (E ++ G) p T → okt (E ++ F ++ G) → has (E ++ F ++ G) p T := by
  sorry

-- Coq 1204: has_weakening1
 theorem has_weakening1 : ∀ {E F G p T}, has E p T → okt (E ++ F ++ G) → has (E ++ F ++ G) p T := by
  sorry

-- Coq 1219: has_weakening_empty
 theorem has_weakening_empty : ∀ {E p T}, has [] p T → okt E → has E p T := by
  sorry

-- Coq 1241: sub_has_narrowing_aux (pair)
theorem sub_has_narrowing_aux :
  (∀ {E0 S T}, sub E0 S T → ∀ {Q E F z P}, E0 = (E ++ ( (z, Q) :: F)) → sub E P Q → sub (E ++ ((z, P) :: F)) S T) ∧
  (∀ {E0 p T}, has E0 p T → ∀ {Q E F z P}, E0 = (E ++ ( (z, Q) :: F)) → sub E P Q → has (E ++ ((z, P) :: F)) p T) := by
  sorry

-- Coq 1276: sub_narrowing
 theorem sub_narrowing : ∀ {Q E F Z P S T}, sub E P Q → sub (E ++ ((Z, Q) :: F)) S T → sub (E ++ ((Z, P) :: F)) S T := by
  sorry

-- Coq 1285: sub_narrowing_empty
 theorem sub_narrowing_empty : ∀ {Q Z P S T}, sub [] P Q → sub ((Z, Q) :: []) S T → sub ((Z, P) :: []) S T := by
  sorry

-- Coq 1302: has_value_var
 theorem has_value_var : ∀ {E u T}, has E u T → (value u ∨ ∃ x, trm_fvar x = u) := by
  sorry

-- Coq 1312: var_typing_has
 theorem var_typing_has : ∀ {E x Q}, typing E (trm_fvar x) Q → has E (trm_fvar x) Q := by
  sorry

-- Coq 1322: val_typing_has
 theorem val_typing_has : ∀ {E u Q}, value u → typing E u Q → has E u Q := by
  sorry

-- Coq 1335: sub_has_through_subst (pair)
theorem sub_has_through_subst :
  (∀ {E0 S T}, sub E0 S T → ∀ {Q E F Z u}, E0 = (E ++ ((Z, Q) :: F)) → (value u ∨ ∃ x, trm_fvar x = u) → typing E u Q →
    sub (E ++ map_subst_t Z u F) (subst_t Z u S) (subst_t Z u T)) ∧
  (∀ {E0 p T}, has E0 p T → ∀ {Q E F Z u}, E0 = (E ++ ((Z, Q) :: F)) → (value u ∨ ∃ x, trm_fvar x = u) → typing E u Q →
    has (E ++ map_subst_t Z u F) (subst_e Z u p) (subst_t Z u T)) := by
  sorry

-- Coq 1402: typing_weakening
 theorem typing_weakening : ∀ {E F G e T}, typing (E ++ G) e T → okt (E ++ F ++ G) → typing (E ++ F ++ G) e T := by
  sorry

-- Coq 1420: typing_narrowing
 theorem typing_narrowing : ∀ {Q E F X P e T}, sub E P Q → typing (E ++ ((X, Q) :: F)) e T → typing (E ++ ((X, P) :: F)) e T := by
  sorry

-- Coq 1438: typing_narrowing_empty
 theorem typing_narrowing_empty : ∀ {Q X P e T}, sub [] P Q → typing ((X, Q) :: []) e T → typing ((X, P) :: []) e T := by
  sorry

-- Coq 1453: typing_through_subst
 theorem typing_through_subst : ∀ {U E F z T e u},
  typing (E ++ ((z, U) :: F)) e T → (value u ∨ ∃ x, trm_fvar x = u) → typing E u U →
  typing (E ++ map_subst_t z u F) (subst_e z u e) (subst_t z u T) := by
  sorry

/- Pseudo-subtyping and canonical forms -/
-- Coq 1545: has_empty_value
 theorem has_empty_value : ∀ {p T}, has [] p T → value p := by
  sorry

-- Coq 1557: psub_sub
 theorem psub_sub : ∀ {S T}, psub S T → sub [] S T := by
  sorry

-- Coq 1603: possible_types_value / wfe / wft
 theorem possible_types_value : ∀ {n p T}, possible_types n p T → value p := by
  sorry

 theorem possible_types_wfe : ∀ {n p T}, possible_types n p T → wfe [] p := by
  sorry

 theorem possible_types_wft : ∀ {n p T}, possible_types n p T → wft [] T := by
  sorry

-- Coq 1648: has_empty_var_false
 theorem has_empty_var_false : ∀ {x T}, has [] (trm_fvar x) T → False := by
  sorry

-- Coq 1661: possible_types_closure_psub
 theorem possible_types_closure_psub : ∀ {n v T U}, possible_types n v T → psub T U → possible_types n v U := by
  sorry

-- Coq 1689: psub_reflexivity
 theorem psub_reflexivity : ∀ {T}, wft [] T → psub T T := by
  sorry

-- Coq 1703: sub_psub_aux (pair)
 theorem sub_psub_aux :
  (∀ {E S T}, sub E S T → E = [] → psub S T) ∧ (∀ {E p T}, has E p T → E = [] → possible_types 0 p T) := by
  sorry

-- Coq 1725: sub_psub
 theorem sub_psub : ∀ {S T}, sub [] S T → psub S T := by
  sorry

-- Coq 1731: possible_types_closure
 theorem possible_types_closure : ∀ {n v T U}, possible_types n v T → sub [] T U → possible_types n v U := by
  sorry

-- Coq 1740: possible_types_typing
 theorem possible_types_typing : ∀ {v T}, typing [] v T → value v → possible_types 1 v T := by
  sorry

-- Coq 1761: typing_inv_abs
 theorem typing_inv_abs : ∀ {S1 e1 T}, typing [] (trm_abs S1 e1) T →
  ∀ U1 U2, sub [] T (typ_all U1 U2) →
    sub [] U1 S1 ∧ ∃ S2, ∃ L : Vars, ∀ x, x ∉ L →
      typing ((x, S1) :: []) (open_e e1 (trm_fvar x)) (open_t S2 (trm_fvar x)) ∧ sub ((x, U1) :: []) (open_t S2 (trm_fvar x)) (open_t U2 (trm_fvar x)) := by
  sorry

-- Coq 1780: canonical forms
 theorem canonical_form_abs : ∀ {t U1 U2}, value t → typing [] t (typ_all U1 U2) → ∃ V, ∃ e1, t = trm_abs V e1 := by
  sorry

 theorem canonical_form_mem : ∀ {t b T}, value t → typing [] t (typ_mem b T) → ∃ V, t = trm_mem V := by
  sorry

-- Coq 1798: typing_through_subst1
 theorem typing_through_subst1 : ∀ {V y v e T},
  typing ((y, V) :: []) e T → value v → typing [] v V →
  typing [] (subst_e y v e) (subst_t y v T) := by
  sorry


/- Well-formedness weakening/narrowing/substitution and env properties -/
-- Coq 628: wf_weaken (pair)
 theorem wf_weaken :
  (∀ {E0 T}, wft E0 T → ∀ {E F G}, E0 = E ++ G → ok (E ++ F ++ G) → wft (E ++ F ++ G) T) ∧
  (∀ {E0 e}, wfe E0 e → ∀ {E F G}, E0 = E ++ G → ok (E ++ F ++ G) → wfe (E ++ F ++ G) e) := by
  sorry

-- Coq 645: wft_weaken
 theorem wft_weaken : ∀ {G T E F}, wft (E ++ G) T → ok (E ++ F ++ G) → wft (E ++ F ++ G) T := by
  sorry

-- Coq 653: wft_weaken_empty
 theorem wft_weaken_empty : ∀ {T E}, wft [] T → ok E → wft E T := by
  sorry

-- Coq 667: wfe_weaken
 theorem wfe_weaken : ∀ {G T E F}, wfe (E ++ G) T → ok (E ++ F ++ G) → wfe (E ++ F ++ G) T := by
  sorry

-- Coq 675: wfe_weaken_empty
 theorem wfe_weaken_empty : ∀ {T E}, wfe [] T → ok E → wfe E T := by
  sorry

-- Coq 691: wf_narrow (pair)
 theorem wf_narrow :
  (∀ {E0 T}, wft E0 T → ∀ {V F U E x}, E0 = (E ++ ((x, V) :: F)) → ok (E ++ ((x, U) :: F)) → wft (E ++ ((x, U) :: F)) T) ∧
  (∀ {E0 e}, wfe E0 e → ∀ {V F U E x}, E0 = (E ++ ((x, V) :: F)) → ok (E ++ ((x, U) :: F)) → wfe (E ++ ((x, U) :: F)) e) := by
  sorry

-- Coq 711: wft_narrow
 theorem wft_narrow : ∀ {V F U T E x}, wft (E ++ ((x, V) :: F)) T → ok (E ++ ((x, U) :: F)) → wft (E ++ ((x, U) :: F)) T := by
  sorry

-- Coq 721: wf_subst (pair)
 theorem wf_subst :
  (∀ {E0 T}, wft E0 T → ∀ {F Q E Z u}, E0 = E ++ ((Z, Q) :: F) → (value u ∨ ∃ x, trm_fvar x = u) → wfe E u → ok (E ++ map_subst_t Z u F) →
    wft (E ++ map_subst_t Z u F) (subst_t Z u T)) ∧
  (∀ {E0 e}, wfe E0 e → ∀ {F Q E Z u}, E0 = E ++ ((Z, Q) :: F) → (value u ∨ ∃ x, trm_fvar x = u) → wfe E u → ok (E ++ map_subst_t Z u F) →
    wfe (E ++ map_subst_t Z u F) (subst_e Z u e)) := by
  sorry

-- Coq 757: wft_subst
 theorem wft_subst : ∀ {F Q E Z u T}, wft (E ++ ((Z, Q) :: F)) T → (value u ∨ ∃ x, trm_fvar x = u) → wfe E u → ok (E ++ map_subst_t Z u F) →
  wft (E ++ map_subst_t Z u F) (subst_t Z u T) := by
  sorry

-- Coq 766: wft_subst1
 theorem wft_subst1 : ∀ {F Q Z u T}, wft ((Z, Q) :: F) T → (value u ∨ ∃ x, trm_fvar x = u) → wfe [] u → ok (map_subst_t Z u F) →
  wft (map_subst_t Z u F) (subst_t Z u T) := by
  sorry

-- Coq 779: wft_subst_empty
 theorem wft_subst_empty : ∀ {Q Z u T}, wft ((Z, Q) :: []) T → (value u ∨ ∃ x, trm_fvar x = u) → wfe [] u → wft [] (subst_t Z u T) := by
  sorry

-- Coq 795: wft_open
 theorem wft_open : ∀ {E u T1 T2}, ok E → wft E (typ_all T1 T2) → (value u ∨ ∃ x, trm_fvar x = u) → wfe E u → wft E (open_t T2 u) := by
  sorry

-- Coq 814: ok_from_okt already stubbed above

/- Relations between okt and wft in environments -/
-- Coq 824: wft_from_env_has
 theorem wft_from_env_has : ∀ {x U E}, okt E → binds x U E → wft E U := by
  sorry

-- Coq 839: wft_from_okt
 theorem wft_from_okt : ∀ {x T E}, okt ((x, T) :: E) → wft E T := by
  sorry

-- Coq 849: wft_weaken_right
 theorem wft_weaken_right : ∀ {T E F}, wft E T → ok (E ++ F) → wft (E ++ F) T := by
  sorry

/- Properties of well-formed environments -/
-- Coq 867: okt_push_inv
 theorem okt_push_inv : ∀ {E x T}, okt ((x, T) :: E) → okt E ∧ wft E T ∧ E.lookup x = none := by
  sorry

-- Coq 875: okt_push_type
 theorem okt_push_type : ∀ {E x T}, okt ((x, T) :: E) → def_type T := by
  sorry

-- Coq 883: okt_narrow
theorem okt_narrow : ∀ {V} (E F : env) {U x}, okt (E ++ ((x, V) :: F)) → wft E U → okt (E ++ ((x, U) :: F)) := by
  sorry

-- Coq 897: okt_subst
theorem okt_subst : ∀ {Q Z u} (E F : env), okt (E ++ ((Z, Q) :: F)) → (value u ∨ ∃ x, trm_fvar x = u) → wfe E u → okt (E ++ map_subst_t Z u F) := by
  sorry

-- Coq 910: okt_subst1
theorem okt_subst1 : ∀ {Q Z u} (F : env), okt (((Z, Q) :: F)) → (value u ∨ ∃ x, trm_fvar x = u) → wfe [] u → okt (map_subst_t Z u F) := by
  sorry

/- Free variable and freshness infrastructure -/
-- Coq 933: notin_fv_open_rec (pair)
 theorem notin_fv_open_rec :
  (∀ {T k y x}, x ∉ fv_t (open_t_rec k (trm_fvar y) T) → x ∉ fv_t T) ∧
  (∀ {e k y x}, x ∉ fv_e (open_e_rec k (trm_fvar y) e) → x ∉ fv_e e) := by
  sorry

-- Coq 943: notin_fv_t_open
 theorem notin_fv_t_open : ∀ {y x T}, x ∉ fv_t (open_t T (trm_fvar y)) → x ∉ fv_t T := by
  sorry

-- Coq 950: notin_fv_e_open
 theorem notin_fv_e_open : ∀ {y x e}, x ∉ fv_e (open_e e (trm_fvar y)) → x ∉ fv_e e := by
  sorry

-- Coq 957: notin_fv_wf_rec (pair)
 theorem notin_fv_wf_rec :
  (∀ {E T} , wft E T → ∀ {x}, x ∉ dom E → x ∉ fv_t T) ∧
  (∀ {E e} , wfe E e → ∀ {x}, x ∉ dom E → x ∉ fv_e e) := by
  sorry

-- Coq 969: notin_fv_wf
 theorem notin_fv_wf : ∀ {E x T}, wft E T → x ∉ dom E → x ∉ fv_t T := by
  sorry

-- Coq 975: map_subst_id
 theorem map_subst_id : ∀ {G z u}, okt G → z ∉ dom G → G = map_subst_t z u G := by
  sorry

/- Regularity of relations -/
-- Coq 989: sub_has_regular (pair)
 theorem sub_has_regular :
  (∀ {E S T}, sub E S T → okt E ∧ wft E S ∧ wft E T) ∧
  (∀ {E p T}, has E p T → okt E ∧ wft E (typ_sel p) ∧ wft E T) := by
  sorry

-- Coq 1003: sub_regular
 theorem sub_regular : ∀ {E S T}, sub E S T → okt E ∧ wft E S ∧ wft E T := by
  sorry

-- Coq 1009: has_regular
 theorem has_regular : ∀ {E p T}, has E p T → okt E ∧ wft E (typ_sel p) ∧ wft E T := by
  sorry

-- Coq 1015: has_regular_e
 theorem has_regular_e : ∀ {E p T}, has E p T → (value p ∨ ∃ x, trm_fvar x = p) ∧ wfe E p := by
  sorry

/- Top-level safety goals -/
-- Coq 1821: Preservation result
theorem preservation_result : preservation := by
  -- TODO: standard preservation using inversion and substitution lemmas
  sorry

-- Coq 1864: Progress result
theorem progress_result : progress := by
  -- TODO: standard progress via canonical forms and inversion
  sorry

end Lp2lc.Active.Ddia
