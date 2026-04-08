/-****************************************************************************
* Ddia (DOT-style calculus) – Theorems (scaffold)
* All proofs are `sorry` placeholders per 1_Scaffold.md; no axioms introduced.
*****************************************************************************-/

import Aesop
import Mathlib.Data.Finset.Basic

import «Lp2lc».Active.Ddia.Def
import «Lp2lc».Active.Ddia.Auxiliary

namespace Lp2lc.Active.Ddia

open Typ Trm DefType DefTerm Wft Wfe Value Sub Has Typing Red

/- Selection of core lemmas stubbed to establish structure. The full list
   is tracked in Proof.progress.md and will be added incrementally. -/


-- A few substitution lemmas
-- We discharge subst_t_type and subst_e_term mutually, relying on distribution lemmas in Auxiliary.lean.
-- A few substitution lemmas (stubs)
-- Coq line 574: Lemma subst_e_term
-- Substitution over terms preserves local closure of terms.
theorem subst_e_term : ∀ {e1 z e2}, DefTerm e1 → DefTerm e2 → DefTerm (subst_e z e2 e1) := by
  -- TODO: mutual induction over terms
  intro _ _ _ _ _; sorry

-- Coq line 568: Lemma subst_t_type (adapted to Ddia: subst over types uses terms)
-- Substitution over types preserves local closure of types.
theorem subst_t_type : ∀ {T z u}, DefType T → DefTerm u → DefType (subst_t z u T) := by
  -- TODO: mutual induction over types/terms
  intro _ _ _ _ _; sorry

/- Section: Properties of Substitutions (Opening, Substitution, Local Closure) -/
-- Opening and substitution infrastructure (typed)
-- Core open_rec lemma (type part)
theorem open_rec_lc_core_t : ∀ (T : Typ) (j : Nat) (v u : Trm) (i : Nat),
  i ≠ j → open_t_rec j v T = open_t_rec i u (open_t_rec j v T) → T = open_t_rec i u T := by
  sorry

-- Core open_rec lemma (term part)
theorem open_rec_lc_core_e : ∀ (e : Trm) (j : Nat) (v u : Trm) (i : Nat),
  i ≠ j → open_e_rec j v e = open_e_rec i u (open_e_rec j v e) → e = open_e_rec i u e := by
  sorry

-- Opening preserves equality for locally closed objects
theorem open_rec_lc_t : ∀ (T : Typ), DefType T → ∀ (u : Trm) (k : Nat), T = open_t_rec k u T := by
  sorry

theorem open_rec_lc_e : ∀ (e : Trm), DefTerm e → ∀ (u : Trm) (k : Nat), e = open_e_rec k u e := by
  sorry

-- Opening with a fresh variable does nothing on types
theorem open_t_var_type : ∀ (x : Var) (T : Typ), DefType T → open_t T (trm_fvar x) = T := by
  sorry

-- Substitution for a fresh name is identity

theorem subst_fresh_t : ∀ (T : Typ) (z : Var) (u : Trm), z ∉ fv_t T → subst_t z u T = T := by
  sorry

theorem subst_fresh_e : ∀ (e : Trm) (z : Var) (u : Trm), z ∉ fv_e e → subst_e z u e = e := by
  sorry

-- Substitution distributes over open_rec

theorem subst_open_rec_t : ∀ (T1 : Typ) (t2 : Trm) (x : Var) (u : Trm) (n : Nat), DefTerm u →
  subst_t x u (open_t_rec n t2 T1) = open_t_rec n (subst_e x u t2) (subst_t x u T1) := by
  sorry

theorem subst_open_rec_e : ∀ (t1 t2 : Trm) (x : Var) (u : Trm) (n : Nat), DefTerm u →
  subst_e x u (open_e_rec n t2 t1) = open_e_rec n (subst_e x u t2) (subst_e x u t1) := by
  sorry

-- Substitution distributes over open (wrappers)

theorem subst_t_open_t : ∀ (T1 : Typ) (t2 : Trm) (x : Var) (u : Trm), DefTerm u →
  subst_t x u (open_t T1 t2) = open_t (subst_t x u T1) (subst_e x u t2) := by
  sorry

theorem subst_e_open_e : ∀ (t1 t2 : Trm) (x : Var) (u : Trm), DefTerm u →
  subst_e x u (open_e t1 t2) = open_e (subst_e x u t1) (subst_e x u t2) := by
  sorry

-- Substitution and open_var commute when names are distinct

theorem subst_t_open_t_var : ∀ (x y : Var) (u : Trm) (T : Typ), y ≠ x → DefTerm u →
  open_t (subst_t x u T) (trm_fvar y) = subst_t x u (open_t T (trm_fvar y)) := by
  sorry

theorem subst_e_open_e_var : ∀ (x y : Var) (u : Trm) (e : Trm), y ≠ x → DefTerm u →
  open_e (subst_e x u e) (trm_fvar y) = subst_e x u (open_e e (trm_fvar y)) := by
  sorry

-- Substitution intro lemmas

theorem subst_t_intro : ∀ (x : Var) (T2 : Typ) (u : Trm), x ∉ fv_t T2 → DefTerm u →
  open_t T2 u = subst_t x u (open_t T2 (trm_fvar x)) := by
  sorry

theorem subst_e_intro : ∀ (x : Var) (t2 : Trm) (u : Trm), x ∉ fv_e t2 → DefTerm u →
  open_e t2 u = subst_e x u (open_e t2 (trm_fvar x)) := by
  sorry

-- Substitutions preserve local closure

theorem subst_lc_t : ∀ (T : Typ), DefType T → ∀ (z : Var) (u : Trm), DefTerm u → DefType (subst_t z u T) := by
  sorry

theorem subst_lc_e : ∀ (e : Trm), DefTerm e → ∀ (z : Var) (u : Trm), DefTerm u → DefTerm (subst_e z u e) := by
  sorry

/- Section: Regularity (terms, Typing, reduction) -/
-- Coq line 596: Lemma value_is_term
theorem value_is_term : ∀ e, Value e → DefTerm e := by
  intro e h; cases h <;> aesop

-- Coq line 614: Lemma wft_type
theorem wft_type : ∀ {E T}, Wft E T → DefType T := by
  -- TODO: will be proved using mutual recursion with wfe_term and regularity lemmas
  intro _ _ _; sorry

-- Coq line 1024: Lemma typing_regular
theorem typing_regular : ∀ {E e T}, Typing E e T → Okt E ∧ Wfe E e ∧ Wft E T := by
  -- TODO: structural cases on Typing
  sorry

-- Coq line 608: wf_lc (mutual regularity)
theorem wf_lc :
  (∀ {E T}, Wft E T → DefType T) ∧
  (∀ {E e}, Wfe E e → DefTerm e) := by
  sorry

-- Coq line 620: wfe_term (projection of wf_lc)
theorem wfe_term : ∀ {E e}, Wfe E e → DefTerm e := by
  intro E e h; -- will use wf_lc in the real proof
  sorry

-- Coq line 814: ok_from_okt
-- Bridge from well-formed environment to abstract ok predicate from Shared
-- (the actual proof will follow the project’s environment invariants)
theorem ok_from_okt : ∀ {E}, Okt E → ok E := by
  intro E _; sorry

-- Coq line 1049: value_regular (alias of value_is_term)
theorem value_regular : ∀ t, Value t → DefTerm t := by
  intro t h; exact value_is_term t h

-- Coq line 1057: red_regular (terms preserved by one-step reduction)
theorem red_regular : ∀ t t', Red t t' → DefTerm t ∧ DefTerm t' := by
  intro _ _ _; sorry

-- Coq line 1815: value_red_contra
theorem value_red_contra : ∀ {e e'}, Value e → Red e e' → False := by
  intro e e' hv hr; sorry

/- Properties of Subtyping -/
-- Coq 1116: sub_reflexivity
theorem sub_reflexivity : ∀ {E T}, Okt E → Wft E T → Sub E T T := by
  intro E T hOk hW; 
  -- TODO: structural induction over hW, cofinite in all-case
  sorry

/- Weakening, narrowing, substitution for Sub/Has and Typing -/
-- Coq lines ~1132: sub_has_weakening (pair)
theorem sub_has_weakening :
  (∀ {E0 S T}, Sub E0 S T → ∀ {E F G}, E0 = E ++ G → Okt (E ++ F ++ G) → Sub (E ++ F ++ G) S T) ∧
  (∀ {E0 p T}, Has E0 p T → ∀ {E F G}, E0 = E ++ G → Okt (E ++ F ++ G) → Has (E ++ F ++ G) p T) := by
  sorry

-- Coq 1158: sub_weakening
 theorem sub_weakening : ∀ {E F G S T}, Sub (E ++ G) S T → Okt (E ++ F ++ G) → Sub (E ++ F ++ G) S T := by
  sorry

-- Coq 1166: sub_weakening1
 theorem sub_weakening1 : ∀ {E F G S T}, Sub E S T → Okt (E ++ F ++ G) → Sub (E ++ F ++ G) S T := by
  sorry

-- Coq 1181: sub_weakening_empty
 theorem sub_weakening_empty : ∀ {E S T}, Sub [] S T → Okt E → Sub E S T := by
  sorry

-- Coq 1196: has_weakening
 theorem has_weakening : ∀ {E F G p T}, Has (E ++ G) p T → Okt (E ++ F ++ G) → Has (E ++ F ++ G) p T := by
  sorry

-- Coq 1204: has_weakening1
 theorem has_weakening1 : ∀ {E F G p T}, Has E p T → Okt (E ++ F ++ G) → Has (E ++ F ++ G) p T := by
  sorry

-- Coq 1219: has_weakening_empty
 theorem has_weakening_empty : ∀ {E p T}, Has [] p T → Okt E → Has E p T := by
  sorry

-- Coq 1241: sub_has_narrowing_aux (pair)
theorem sub_has_narrowing_aux :
  (∀ {E0 S T}, Sub E0 S T → ∀ {Q E F z P}, E0 = (E ++ ( (z, Q) :: F)) → Sub E P Q → Sub (E ++ ((z, P) :: F)) S T) ∧
  (∀ {E0 p T}, Has E0 p T → ∀ {Q E F z P}, E0 = (E ++ ( (z, Q) :: F)) → Sub E P Q → Has (E ++ ((z, P) :: F)) p T) := by
  sorry

-- Coq 1276: sub_narrowing
 theorem sub_narrowing : ∀ {Q E F Z P S T}, Sub E P Q → Sub (E ++ ((Z, Q) :: F)) S T → Sub (E ++ ((Z, P) :: F)) S T := by
  sorry

-- Coq 1285: sub_narrowing_empty
 theorem sub_narrowing_empty : ∀ {Q Z P S T}, Sub [] P Q → Sub ((Z, Q) :: []) S T → Sub ((Z, P) :: []) S T := by
  sorry

-- Coq 1302: has_value_var
 theorem has_value_var : ∀ {E u T}, Has E u T → (Value u ∨ ∃ x, trm_fvar x = u) := by
  sorry

-- Coq 1312: var_typing_has
 theorem var_typing_has : ∀ {E x Q}, Typing E (trm_fvar x) Q → Has E (trm_fvar x) Q := by
  sorry

-- Coq 1322: val_typing_has
 theorem val_typing_has : ∀ {E u Q}, Value u → Typing E u Q → Has E u Q := by
  sorry

-- Coq 1335: sub_has_through_subst (pair)
theorem sub_has_through_subst :
  (∀ {E0 S T}, Sub E0 S T → ∀ {Q E F Z u}, E0 = (E ++ ((Z, Q) :: F)) → (Value u ∨ ∃ x, trm_fvar x = u) → Typing E u Q →
    Sub (E ++ map_subst_t Z u F) (subst_t Z u S) (subst_t Z u T)) ∧
  (∀ {E0 p T}, Has E0 p T → ∀ {Q E F Z u}, E0 = (E ++ ((Z, Q) :: F)) → (Value u ∨ ∃ x, trm_fvar x = u) → Typing E u Q →
    Has (E ++ map_subst_t Z u F) (subst_e Z u p) (subst_t Z u T)) := by
  sorry

-- Coq 1402: typing_weakening
 theorem typing_weakening : ∀ {E F G e T}, Typing (E ++ G) e T → Okt (E ++ F ++ G) → Typing (E ++ F ++ G) e T := by
  sorry

-- Coq 1420: typing_narrowing
 theorem typing_narrowing : ∀ {Q E F X P e T}, Sub E P Q → Typing (E ++ ((X, Q) :: F)) e T → Typing (E ++ ((X, P) :: F)) e T := by
  sorry

-- Coq 1438: typing_narrowing_empty
 theorem typing_narrowing_empty : ∀ {Q X P e T}, Sub [] P Q → Typing ((X, Q) :: []) e T → Typing ((X, P) :: []) e T := by
  sorry

-- Coq 1453: typing_through_subst
 theorem typing_through_subst : ∀ {U E F z T e u},
  Typing (E ++ ((z, U) :: F)) e T → (Value u ∨ ∃ x, trm_fvar x = u) → Typing E u U →
  Typing (E ++ map_subst_t z u F) (subst_e z u e) (subst_t z u T) := by
  sorry

/- Pseudo-subtyping and canonical forms -/
-- Coq 1545: has_empty_value
 theorem has_empty_value : ∀ {p T}, Has [] p T → Value p := by
  sorry

-- Coq 1557: psub_sub
 theorem psub_sub : ∀ {S T}, Psub S T → Sub [] S T := by
  sorry

-- Coq 1603: possible_types_value / Wfe / Wft
 theorem possible_types_value : ∀ {n p T}, PossibleTypes n p T → Value p := by
  sorry

 theorem possible_types_wfe : ∀ {n p T}, PossibleTypes n p T → Wfe [] p := by
  sorry

 theorem possible_types_wft : ∀ {n p T}, PossibleTypes n p T → Wft [] T := by
  sorry

-- Coq 1648: has_empty_var_false
 theorem has_empty_var_false : ∀ {x T}, Has [] (trm_fvar x) T → False := by
  sorry

-- Coq 1661: possible_types_closure_psub
 theorem possible_types_closure_psub : ∀ {n v T U}, PossibleTypes n v T → Psub T U → PossibleTypes n v U := by
  sorry

-- Coq 1689: psub_reflexivity
 theorem psub_reflexivity : ∀ {T}, Wft [] T → Psub T T := by
  sorry

-- Coq 1703: sub_psub_aux (pair)
 theorem sub_psub_aux :
  (∀ {E S T}, Sub E S T → E = [] → Psub S T) ∧ (∀ {E p T}, Has E p T → E = [] → PossibleTypes 0 p T) := by
  sorry

-- Coq 1725: sub_psub
 theorem sub_psub : ∀ {S T}, Sub [] S T → Psub S T := by
  sorry

-- Coq 1731: possible_types_closure
 theorem possible_types_closure : ∀ {n v T U}, PossibleTypes n v T → Sub [] T U → PossibleTypes n v U := by
  sorry

-- Coq 1740: possible_types_typing
 theorem possible_types_typing : ∀ {v T}, Typing [] v T → Value v → PossibleTypes 1 v T := by
  sorry

-- Coq 1761: typing_inv_abs
 theorem typing_inv_abs : ∀ {S1 e1 T}, Typing [] (trm_abs S1 e1) T →
  ∀ U1 U2, Sub [] T (typ_all U1 U2) →
    Sub [] U1 S1 ∧ ∃ S2, ∃ L : Vars, ∀ x, x ∉ L →
      Typing ((x, S1) :: []) (open_e e1 (trm_fvar x)) (open_t S2 (trm_fvar x)) ∧ Sub ((x, U1) :: []) (open_t S2 (trm_fvar x)) (open_t U2 (trm_fvar x)) := by
  sorry

-- Coq 1780: canonical forms
 theorem canonical_form_abs : ∀ {t U1 U2}, Value t → Typing [] t (typ_all U1 U2) → ∃ V, ∃ e1, t = trm_abs V e1 := by
  sorry

 theorem canonical_form_mem : ∀ {t b T}, Value t → Typing [] t (typ_mem b T) → ∃ V, t = trm_mem V := by
  sorry

-- Coq 1798: typing_through_subst1
 theorem typing_through_subst1 : ∀ {V y v e T},
  Typing ((y, V) :: []) e T → Value v → Typing [] v V →
  Typing [] (subst_e y v e) (subst_t y v T) := by
  sorry


/- Well-formedness weakening/narrowing/substitution and Env properties -/
-- Coq 628: wf_weaken (pair)
 theorem wf_weaken :
  (∀ {E0 T}, Wft E0 T → ∀ {E F G}, E0 = E ++ G → ok (E ++ F ++ G) → Wft (E ++ F ++ G) T) ∧
  (∀ {E0 e}, Wfe E0 e → ∀ {E F G}, E0 = E ++ G → ok (E ++ F ++ G) → Wfe (E ++ F ++ G) e) := by
  sorry

-- Coq 645: wft_weaken
 theorem wft_weaken : ∀ {G T E F}, Wft (E ++ G) T → ok (E ++ F ++ G) → Wft (E ++ F ++ G) T := by
  sorry

-- Coq 653: wft_weaken_empty
 theorem wft_weaken_empty : ∀ {T E}, Wft [] T → ok E → Wft E T := by
  sorry

-- Coq 667: wfe_weaken
 theorem wfe_weaken : ∀ {G T E F}, Wfe (E ++ G) T → ok (E ++ F ++ G) → Wfe (E ++ F ++ G) T := by
  sorry

-- Coq 675: wfe_weaken_empty
 theorem wfe_weaken_empty : ∀ {T E}, Wfe [] T → ok E → Wfe E T := by
  sorry

-- Coq 691: wf_narrow (pair)
 theorem wf_narrow :
  (∀ {E0 T}, Wft E0 T → ∀ {V F U E x}, E0 = (E ++ ((x, V) :: F)) → ok (E ++ ((x, U) :: F)) → Wft (E ++ ((x, U) :: F)) T) ∧
  (∀ {E0 e}, Wfe E0 e → ∀ {V F U E x}, E0 = (E ++ ((x, V) :: F)) → ok (E ++ ((x, U) :: F)) → Wfe (E ++ ((x, U) :: F)) e) := by
  sorry

-- Coq 711: wft_narrow
 theorem wft_narrow : ∀ {V F U T E x}, Wft (E ++ ((x, V) :: F)) T → ok (E ++ ((x, U) :: F)) → Wft (E ++ ((x, U) :: F)) T := by
  sorry

-- Coq 721: wf_subst (pair)
 theorem wf_subst :
  (∀ {E0 T}, Wft E0 T → ∀ {F Q E Z u}, E0 = E ++ ((Z, Q) :: F) → (Value u ∨ ∃ x, trm_fvar x = u) → Wfe E u → ok (E ++ map_subst_t Z u F) →
    Wft (E ++ map_subst_t Z u F) (subst_t Z u T)) ∧
  (∀ {E0 e}, Wfe E0 e → ∀ {F Q E Z u}, E0 = E ++ ((Z, Q) :: F) → (Value u ∨ ∃ x, trm_fvar x = u) → Wfe E u → ok (E ++ map_subst_t Z u F) →
    Wfe (E ++ map_subst_t Z u F) (subst_e Z u e)) := by
  sorry

-- Coq 757: wft_subst
 theorem wft_subst : ∀ {F Q E Z u T}, Wft (E ++ ((Z, Q) :: F)) T → (Value u ∨ ∃ x, trm_fvar x = u) → Wfe E u → ok (E ++ map_subst_t Z u F) →
  Wft (E ++ map_subst_t Z u F) (subst_t Z u T) := by
  sorry

-- Coq 766: wft_subst1
 theorem wft_subst1 : ∀ {F Q Z u T}, Wft ((Z, Q) :: F) T → (Value u ∨ ∃ x, trm_fvar x = u) → Wfe [] u → ok (map_subst_t Z u F) →
  Wft (map_subst_t Z u F) (subst_t Z u T) := by
  sorry

-- Coq 779: wft_subst_empty
 theorem wft_subst_empty : ∀ {Q Z u T}, Wft ((Z, Q) :: []) T → (Value u ∨ ∃ x, trm_fvar x = u) → Wfe [] u → Wft [] (subst_t Z u T) := by
  sorry

-- Coq 795: wft_open
 theorem wft_open : ∀ {E u T1 T2}, ok E → Wft E (typ_all T1 T2) → (Value u ∨ ∃ x, trm_fvar x = u) → Wfe E u → Wft E (open_t T2 u) := by
  sorry

-- Coq 814: ok_from_okt already stubbed above

/- Relations between Okt and Wft in environments -/
-- Coq 824: wft_from_env_has
 theorem wft_from_env_has : ∀ {x U E}, Okt E → binds x U E → Wft E U := by
  sorry

-- Coq 839: wft_from_okt
 theorem wft_from_okt : ∀ {x T E}, Okt ((x, T) :: E) → Wft E T := by
  sorry

-- Coq 849: wft_weaken_right
 theorem wft_weaken_right : ∀ {T E F}, Wft E T → ok (E ++ F) → Wft (E ++ F) T := by
  sorry

/- Properties of well-formed environments -/
-- Coq 867: okt_push_inv
 theorem okt_push_inv : ∀ {E x T}, Okt ((x, T) :: E) → Okt E ∧ Wft E T ∧ E.lookup x = none := by
  sorry

-- Coq 875: okt_push_type
 theorem okt_push_type : ∀ {E x T}, Okt ((x, T) :: E) → DefType T := by
  sorry

-- Coq 883: okt_narrow
theorem okt_narrow : ∀ {V} (E F : Env) {U x}, Okt (E ++ ((x, V) :: F)) → Wft E U → Okt (E ++ ((x, U) :: F)) := by
  sorry

-- Coq 897: okt_subst
theorem okt_subst : ∀ {Q Z u} (E F : Env), Okt (E ++ ((Z, Q) :: F)) → (Value u ∨ ∃ x, trm_fvar x = u) → Wfe E u → Okt (E ++ map_subst_t Z u F) := by
  sorry

-- Coq 910: okt_subst1
theorem okt_subst1 : ∀ {Q Z u} (F : Env), Okt (((Z, Q) :: F)) → (Value u ∨ ∃ x, trm_fvar x = u) → Wfe [] u → Okt (map_subst_t Z u F) := by
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
  (∀ {E T} , Wft E T → ∀ {x}, x ∉ dom E → x ∉ fv_t T) ∧
  (∀ {E e} , Wfe E e → ∀ {x}, x ∉ dom E → x ∉ fv_e e) := by
  sorry

-- Coq 969: notin_fv_wf
 theorem notin_fv_wf : ∀ {E x T}, Wft E T → x ∉ dom E → x ∉ fv_t T := by
  sorry

-- Coq 975: map_subst_id
 theorem map_subst_id : ∀ {G z u}, Okt G → z ∉ dom G → G = map_subst_t z u G := by
  sorry

/- Regularity of relations -/
-- Coq 989: sub_has_regular (pair)
 theorem sub_has_regular :
  (∀ {E S T}, Sub E S T → Okt E ∧ Wft E S ∧ Wft E T) ∧
  (∀ {E p T}, Has E p T → Okt E ∧ Wft E (typ_sel p) ∧ Wft E T) := by
  sorry

-- Coq 1003: sub_regular
 theorem sub_regular : ∀ {E S T}, Sub E S T → Okt E ∧ Wft E S ∧ Wft E T := by
  sorry

-- Coq 1009: has_regular
 theorem has_regular : ∀ {E p T}, Has E p T → Okt E ∧ Wft E (typ_sel p) ∧ Wft E T := by
  sorry

-- Coq 1015: has_regular_e
 theorem has_regular_e : ∀ {E p T}, Has E p T → (Value p ∨ ∃ x, trm_fvar x = p) ∧ Wfe E p := by
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
