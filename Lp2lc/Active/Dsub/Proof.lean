/- Dsub Proof scaffolds

This file mirrors the lemmas in Coq Lp2lc_coq/Active/Dsub.v and provides theorem
statements with `sorry` placeholders. No axioms. Keep the original order.
-/

import Std
import «Lp2lc».Active.Dsub.Def
import «Lp2lc».Active.Dsub.Auxiliary

namespace Lp2lc.Active.Dsub

-- The proofs are extensive; here we set up a first batch of scaffolds. More will
-- be appended preserving Coq order and names (splitting /\ into suffix _t/_e
-- variants where needed).

-- Coq line 395: Lemma open_rec_lc_core (split into type/term halves)
-- Split naming: _t for types, _e for terms

theorem open_rec_lc_core_t : ∀ T j v u i,
  i ≠ j →
  open_t_rec j v T = open_t_rec i u (open_t_rec j v T) →
  T = open_t_rec i u T := by
  -- TODO: ported from Coq open_rec_lc_core (type part)
  sorry

theorem open_rec_lc_core_e : ∀ e j v u i,
  i ≠ j →
  open_e_rec j v e = open_e_rec i u (open_e_rec j v e) →
  e = open_e_rec i u e := by
  -- TODO: ported from Coq open_rec_lc_core (term part)
  sorry

-- Coq line 409: Lemma open_rec_lc (split)

theorem open_rec_lc_t : ∀ T,
  DefType T → ∀ u k, T = open_t_rec k u T := by
  -- TODO
  sorry

theorem open_rec_lc_e : ∀ e,
  DefTerm e → ∀ u k, e = open_e_rec k u e := by
  -- TODO
  sorry

-- Coq line 418: Lemma open_t_var_type

theorem open_t_var_type : ∀ x T,
  DefType T → open_t T (Trm.trm_fvar x) = T := by
  -- TODO
  sorry

-- Coq lines 426-433: subst_fresh (split)

theorem subst_fresh_t : ∀ T z u,
  z ∉ fv_t T → subst_t z u T = T := by
  -- TODO
  sorry

theorem subst_fresh_e : ∀ e z u,
  z ∉ fv_e e → subst_e z u e = e := by
  -- TODO
  sorry

-- Coq lines 541–548: value_is_term

theorem value_is_term : ∀ e, Value e -> DefTerm e := by
  intro e h
  cases h with
  | value_abs V e1 hterm =>
    exact hterm
  | value_mem V hterm =>
    exact hterm

-- Coq lines 548–564: wf_lc split
-- Prove wft_type and wfe_term structurally (no mutual recursion cycle),
-- then define wf_lc_t/e as wrappers.

theorem wft_type : ∀ E T, Wft E T → DefType T := by
  -- TODO
  sorry


theorem wfe_term : ∀ E e, Wfe E e → DefTerm e := by
  -- TODO
  sorry


theorem wf_lc_t : ∀ E T, Wft E T -> DefType T := by
  -- TODO
  sorry


theorem wf_lc_e : ∀ E e, Wfe E e -> DefTerm e := by
  -- TODO
  sorry

-- Coq lines 568–613: weakening for Wft/Wfe

theorem wft_weaken : ∀ G T E F,
  Wft (E ++ G) T → ok (E ++ F ++ G) → Wft (E ++ F ++ G) T := by
  -- TODO
  sorry

theorem wfe_weaken : ∀ G e E F,
  Wfe (E ++ G) e → ok (E ++ F ++ G) → Wfe (E ++ F ++ G) e := by
  -- TODO
  sorry

-- Coq lines 757–764: ok_from_okt

theorem ok_from_okt : ∀ E, Okt E → ok E := by
  -- TODO
  sorry

-- Coq lines 782–788: wft_from_okt (adapted)

theorem wft_from_okt : ∀ x T E, Okt ((x, T) :: E) → Wft E T := by
  -- TODO
  sorry

-- Coq lines 792–800: wft_weaken_right

theorem wft_weaken_right : ∀ T E F,
  Wft E T → ok (E ++ F) → Wft (E ++ F) T := by
  -- TODO
  sorry

-- Coq lines 939–963: regularity of Sub/Has and Typing

theorem sub_regular : ∀ E S T,
  Sub E S T → Okt E ∧ Wft E S ∧ Wft E T := by
  -- TODO
  sorry

theorem has_regular : ∀ E p T,
  Has E p T → Okt E ∧ Wft E (Typ.typ_sel p) ∧ Wft E T := by
  -- TODO
  sorry

theorem has_regular_e : ∀ E p T,
  Has E p T → (Value p ∨ ∃ x, Trm.trm_fvar x = p) ∧ Wfe E p := by
  -- TODO
  sorry

-- Coq lines 974–995: typing_regular and value_regular

theorem typing_regular : ∀ E e T,
  Typing E e T → Okt E ∧ Wfe E e ∧ Wft E T := by
  -- TODO
  sorry

theorem value_regular : ∀ t, Value t → DefTerm t := by
  intro t h
  exact value_is_term t h

-- Coq lines 1006–1012: red_regular

theorem red_regular : ∀ t t',
  Red t t' → DefTerm t ∧ DefTerm t' := by
  -- TODO
  sorry

-- Coq lines 1066–1075: sub_reflexivity

theorem sub_reflexivity : ∀ E T,
  Okt E → Wft E T → Sub E T T := by
  -- TODO
  sorry

-- Coq lines 1080–1160: weakening for Sub/Has

theorem sub_weakening : ∀ E F G S T,
  Sub (E ++ G) S T → Okt (E ++ F ++ G) → Sub (E ++ F ++ G) S T := by
  -- TODO
  sorry


theorem has_weakening : ∀ E F G p T,
  Has (E ++ G) p T → Okt (E ++ F ++ G) → Has (E ++ F ++ G) p T := by
  -- TODO
  sorry

-- Coq lines 1334–1385: Typing weakening/narrowing

theorem typing_weakening : ∀ E F G e T,
  Typing (E ++ G) e T → Okt (E ++ F ++ G) → Typing (E ++ F ++ G) e T := by
  -- TODO
  sorry


theorem typing_narrowing : ∀ Q E F X P e T,
  Sub E P Q → Typing (E ++ [(X, Q)] ++ F) e T → Typing (E ++ [(X, P)] ++ F) e T := by
  -- TODO
  sorry


theorem typing_narrowing_empty : ∀ Q X P e T,
  Sub [] P Q → Typing ([(X, Q)]) e T → Typing ([(X, P)]) e T := by
  -- TODO
  sorry

-- Coq lines 1385–1414: Typing through substitution

theorem typing_through_subst : ∀ U E F z T e u,
  Typing (E ++ [(z, U)] ++ F) e T →
  (Value u ∨ ∃ x, Trm.trm_fvar x = u) → Typing E u U →
  Typing (E ++ map_subst_t z u F) (subst_e z u e) (subst_t z u T) := by
  -- TODO
  sorry

-- Coq lines 1685–1698: canonical forms

theorem canonical_form_abs : ∀ t U1 U2,
  Value t → Typing [] t (Typ.typ_all U1 U2) → ∃ V e1, t = Trm.trm_abs V e1 := by
  -- TODO
  sorry


theorem canonical_form_mem : ∀ t b T,
  Value t → Typing [] t (Typ.typ_mem b T) → ∃ V, t = Trm.trm_mem V := by
  -- TODO
  sorry

-- Coq lines 1699–1697 and others: typing_through_subst1

theorem typing_through_subst1 : ∀ V y v e T,
  Typing ([(y, V)]) e T → Value v → Typing [] v V →
  Typing [] (subst_e y v e) (subst_t y v T) := by
  -- TODO
  sorry

-- Coq lines 1703–1710: value_red_contra and preservation_result

theorem value_red_contra : ∀ e e', Value e → Red e e' → False := by
  -- TODO
  sorry


theorem preservation_result : preservation := by
  -- TODO
  sorry

-- Coq lines 1751–1773: progress_result

theorem progress_result : progress := by
  -- TODO
  sorry

-- Additional scaffolds from Dsub.v to complete coverage

-- Coq lines 434–445: subst_open_rec (split)

theorem subst_open_rec_t : ∀ T1 t2 x u n, DefTerm u →
  subst_t x u (open_t_rec n t2 T1) =
  open_t_rec n (subst_e x u t2) (subst_t x u T1) := by
  -- TODO
  sorry

 theorem subst_open_rec_e : ∀ t1 t2 x u n, DefTerm u →
  subst_e x u (open_e_rec n t2 t1) =
  open_e_rec n (subst_e x u t2) (subst_e x u t1) := by
  -- TODO
  sorry

-- Coq lines 447–459
 theorem subst_t_open_t : ∀ T1 t2 x u, DefTerm u →
   subst_t x u (open_t T1 t2) =
   open_t (subst_t x u T1) (subst_e x u t2) := by
   -- TODO
   sorry
 
 theorem subst_e_open_e : ∀ t1 t2 x u, DefTerm u →
   subst_e x u (open_e t1 t2) =
   open_e (subst_e x u t1) (subst_e x u t2) := by
   -- TODO
   sorry

-- Coq lines 461–475
theorem subst_t_open_t_var : ∀ (x y : Var) (u : Trm) (T : Typ), y ≠ x → DefTerm u →
  open_t (subst_t x u T) (Trm.trm_fvar y) = subst_t x u (open_t T (Trm.trm_fvar y)) := by
  -- TODO
  sorry

theorem subst_e_open_e_var : ∀ (x y : Var) (u : Trm) (e : Trm), y ≠ x → DefTerm u →
  open_e (subst_e x u e) (Trm.trm_fvar y) = subst_e x u (open_e e (Trm.trm_fvar y)) := by
  -- TODO
  sorry

-- Coq lines 477–494
theorem subst_t_intro : ∀ x T2 u,
  x ∉ fv_t T2 → DefTerm u →
  open_t T2 u = subst_t x u (T2 open_t_var x) := by
  -- TODO
  sorry

theorem subst_e_intro : ∀ x t2 u,
  x ∉ fv_e t2 → DefTerm u →
  open_e t2 u = subst_e x u (t2 open_e_var x) := by
  -- TODO
  sorry

-- Coq lines 498–513: substitutions preserve local closure (split)
theorem subst_lc_t : ∀ T, DefType T → ∀ z u, DefTerm u → DefType (subst_t z u T) := by
  -- TODO
  sorry

theorem subst_lc_e : ∀ e, DefTerm e → ∀ z u, DefTerm u → DefTerm (subst_e z u e) := by
  -- TODO
  sorry

-- Coq lines 508–534: corollaries
theorem subst_e_value : ∀ e1 z e2,
  Value e1 → DefTerm e2 → Value (subst_e z e2 e1) := by
  -- TODO
  sorry

-- Coq lines 875–934: notin_fv lemmas and map_subst identity
theorem notin_fv_open_rec_t : ∀ T k y x,
  x ∉ fv_t (open_t_rec k (Trm.trm_fvar y) T) → x ∉ fv_t T := by
  -- TODO
  sorry

theorem notin_fv_open_rec_e : ∀ e k y x,
  x ∉ fv_e (open_e_rec k (Trm.trm_fvar y) e) → x ∉ fv_e e := by
  -- TODO
  sorry

theorem notin_fv_t_open : ∀ y x T,
  x ∉ fv_t (T open_t_var y) → x ∉ fv_t T := by
  -- TODO
  sorry

theorem notin_fv_e_open : ∀ y x e,
  x ∉ fv_e (e open_e_var y) → x ∉ fv_e e := by
  -- TODO
  sorry

theorem notin_fv_wf_t : ∀ E T, Wft E T → ∀ x, x ∉ dom E → x ∉ fv_t T := by
  -- TODO
  sorry

theorem notin_fv_wf_e : ∀ E e, Wfe E e → ∀ x, x ∉ dom E → x ∉ fv_e e := by
  -- TODO
  sorry

theorem notin_fv_wf : ∀ E x T,
  Wft E T → x ∉ dom E → x ∉ fv_t T := by
  -- TODO
  sorry

theorem map_subst_t_id : ∀ G z u,
  Okt G → z ∉ dom G → G = map_subst_t z u G := by
  -- TODO
  sorry

-- Coq lines 755–873: environment lemmas
theorem binds_weaken : ∀ (x : Var) (T : Typ) (E F G : Env),
  List.lookup x (E ++ G) = some T → List.lookup x (E ++ F ++ G) = some T := by
  -- TODO
  sorry

theorem wft_weaken_empty : ∀ T E,
  Wft [] T → ok E → Wft E T := by
  -- TODO
  sorry

theorem wfe_weaken_empty : ∀ e E,
  Wfe [] e → ok E → Wfe E e := by
  -- TODO
  sorry

theorem wf_narrow_t : ∀ E0 T, Wft E0 T → ∀ V F U E x,
  E0 = (E ++ [(x, V)] ++ F) → ok (E ++ [(x, U)] ++ F) → Wft (E ++ [(x, U)] ++ F) T := by
  -- TODO
  sorry

theorem wf_narrow_e : ∀ E0 e, Wfe E0 e → ∀ V F U E x,
  E0 = (E ++ [(x, V)] ++ F) → ok (E ++ [(x, U)] ++ F) → Wfe (E ++ [(x, U)] ++ F) e := by
  -- TODO
  sorry

theorem wft_narrow : ∀ V F U T E x,
  Wft (E ++ [(x, V)] ++ F) T → ok (E ++ [(x, U)] ++ F) → Wft (E ++ [(x, U)] ++ F) T := by
  -- TODO
  sorry

theorem wf_subst_t : ∀ E0 T, Wft E0 T → ∀ F Q E Z u,
  E0 = E ++ [(Z, Q)] ++ F → (Value u ∨ ∃ x, Trm.trm_fvar x = u) → Wfe E u →
  ok (E ++ map_subst_t Z u F) → Wft (E ++ map_subst_t Z u F) (subst_t Z u T) := by
  -- TODO
  sorry

theorem wf_subst_e : ∀ E0 e, Wfe E0 e → ∀ F Q E Z u,
  E0 = E ++ [(Z, Q)] ++ F → (Value u ∨ ∃ x, Trm.trm_fvar x = u) → Wfe E u →
  ok (E ++ map_subst_t Z u F) → Wfe (E ++ map_subst_t Z u F) (subst_e Z u e) := by
  -- TODO
  sorry

theorem wft_subst : ∀ F Q E Z u T,
  Wft (E ++ [(Z, Q)] ++ F) T → (Value u ∨ ∃ x, Trm.trm_fvar x = u) → Wfe E u →
  ok (E ++ map_subst_t Z u F) → Wft (E ++ map_subst_t Z u F) (subst_t Z u T) := by
  -- TODO
  sorry

theorem wft_subst1 : ∀ F Q Z u T,
  Wft ([(Z, Q)] ++ F) T → (Value u ∨ ∃ x, Trm.trm_fvar x = u) → Wfe [] u →
  ok (map_subst_t Z u F) → Wft (map_subst_t Z u F) (subst_t Z u T) := by
  -- TODO
  sorry

theorem wft_subst_empty : ∀ Q Z u T,
  Wft ([(Z, Q)]) T → (Value u ∨ ∃ x, Trm.trm_fvar x = u) → Wfe [] u →
  Wft [] (subst_t Z u T) := by
  -- TODO
  sorry

theorem wft_open : ∀ E u T1 T2,
  ok E → Wft E (Typ.typ_all T1 T2) → (Value u ∨ ∃ x, Trm.trm_fvar x = u) → Wfe E u →
  Wft E (open_t T2 u) := by
  -- TODO
  sorry

-- Coq lines 805–873: Okt lemmas
theorem okt_push_inv : ∀ E x T,
  Okt ((x, T) :: E) → Okt E ∧ Wft E T ∧ E.lookup x = none := by
  -- TODO
  sorry

theorem okt_push_type : ∀ E x T,
  Okt ((x, T) :: E) → DefType T := by
  -- TODO
  sorry

theorem okt_narrow : ∀ V (E F : Env) U x,
  Okt (E ++ [(x, V)] ++ F) → Wft E U → Okt (E ++ [(x, U)] ++ F) := by
  -- TODO
  sorry

theorem okt_strengthen : ∀ x T E F,
  Okt (E ++ [(x, T)] ++ F) → Okt (E ++ F) := by
  -- TODO
  sorry

theorem okt_subst : ∀ Q Z u (E F : Env),
  Okt (E ++ [(Z, Q)] ++ F) → (Value u ∨ ∃ x, Trm.trm_fvar x = u) → Wfe E u →
  Okt (E ++ map_subst_t Z u F) := by
  -- TODO
  sorry

theorem okt_subst1 : ∀ Q Z u (F : Env),
  Okt ([(Z, Q)] ++ F) → (Value u ∨ ∃ x, Trm.trm_fvar x = u) → Wfe [] u →
  Okt (map_subst_t Z u F) := by
  -- TODO
  sorry

-- Coq lines 1080–1160 variants: weakening 1/empty and Has

theorem sub_weakening1 : ∀ E F G S T,
  Sub E S T → Okt (E ++ F ++ G) → Sub (E ++ F ++ G) S T := by
  -- TODO
  sorry

theorem sub_weakening_empty : ∀ E S T,
  Sub [] S T → Okt E → Sub E S T := by
  -- TODO
  sorry

theorem has_weakening1 : ∀ E F G p T,
  Has E p T → Okt (E ++ F ++ G) → Has (E ++ F ++ G) p T := by
  -- TODO
  sorry

theorem has_weakening_empty : ∀ E p T,
  Has [] p T → Okt E → Has E p T := by
  -- TODO
  sorry

-- Coq lines 1178–1234: Narrowing and transitivity
theorem sub_has_narrowing_aux_t : ∀ E0 S T, Sub E0 S T → ∀ Q E F z P,
  E0 = (E ++ [(z, Q)] ++ F) → Sub E P Q → Sub (E ++ [(z, P)] ++ F) S T := by
  -- TODO
  sorry

theorem sub_has_narrowing_aux_e : ∀ E0 p T, Has E0 p T → ∀ Q E F z P,
  E0 = (E ++ [(z, Q)] ++ F) → Sub E P Q → Has (E ++ [(z, P)] ++ F) p T := by
  -- TODO
  sorry

theorem sub_narrowing : ∀ Q E F z P S T,
  Sub E P Q → Sub (E ++ [(z, Q)] ++ F) S T → Sub (E ++ [(z, P)] ++ F) S T := by
  -- TODO
  sorry

theorem sub_narrowing_empty : ∀ Q z P S T,
  Sub [] P Q → Sub ([(z, Q)]) S T → Sub ([(z, P)]) S T := by
  -- TODO
  sorry

-- Coq lines 1240–1326: substitution preserves subtyping
theorem has_value_var : ∀ E u T,
  Has E u T → (Value u ∨ ∃ x, Trm.trm_fvar x = u) := by
  -- TODO
  sorry

theorem var_typing_has : ∀ E x Q,
  Typing E (Trm.trm_fvar x) Q → Has E (Trm.trm_fvar x) Q := by
  -- TODO
  sorry

theorem val_typing_has : ∀ E u Q,
  Value u → Typing E u Q → Has E u Q := by
  -- TODO
  sorry

theorem sub_has_through_subst_t : ∀ E0 S T, Sub E0 S T → ∀ Q E F Z u,
  E0 = (E ++ [(Z, Q)] ++ F) → (Value u ∨ ∃ x, Trm.trm_fvar x = u) → Typing E u Q →
  Sub (E ++ map_subst_t Z u F) (subst_t Z u S) (subst_t Z u T) := by
  -- TODO
  sorry

theorem sub_has_through_subst_e : ∀ E0 p T, Has E0 p T → ∀ Q E F Z u,
  E0 = (E ++ [(Z, Q)] ++ F) → (Value u ∨ ∃ x, Trm.trm_fvar x = u) → Typing E u Q →
  Has (E ++ map_subst_t Z u F) (subst_e Z u p) (subst_t Z u T) := by
  -- TODO
  sorry

-- Coq lines 1453–1663: Psub and PossibleTypes lemmas
theorem has_empty_value : ∀ p T,
  Has [] p T → Value p := by
  -- TODO
  sorry

theorem psub_sub : ∀ S T,
  Psub S T → Sub [] S T := by
  -- TODO
  sorry

theorem possible_types_value : ∀ n p T,
  PossibleTypes n p T → Value p := by
  -- TODO
  sorry

theorem possible_types_wfe : ∀ n p T,
  PossibleTypes n p T → Wfe [] p := by
  -- TODO
  sorry

theorem possible_types_wft : ∀ n p T,
  PossibleTypes n p T → Wft [] T := by
  -- TODO
  sorry

theorem has_empty_var_false : ∀ x T,
  Has [] (Trm.trm_fvar x) T → False := by
  -- TODO
  sorry

theorem possible_types_closure_psub : ∀ n v T U,
  PossibleTypes n v T → Psub T U → PossibleTypes n v U := by
  -- TODO
  sorry

theorem psub_reflexivity : ∀ T,
  Wft [] T → Psub T T := by
  -- TODO
  sorry

theorem sub_psub_aux_t : ∀ E S T, Sub E S T → E = [] → Psub S T := by
  -- TODO
  sorry

theorem sub_psub_aux_e : ∀ E p T, Has E p T → E = [] → PossibleTypes 0 p T := by
  -- TODO
  sorry

theorem sub_psub : ∀ S T,
  Sub [] S T → Psub S T := by
  -- TODO
  sorry

theorem possible_types_closure : ∀ n v T U,
  PossibleTypes n v T → Sub [] T U → PossibleTypes n v U := by
  -- TODO
  sorry

theorem possible_types_typing : ∀ v T,
  Typing [] v T → Value v → PossibleTypes 1 v T := by
  -- TODO
  sorry

theorem typing_inv_abs : ∀ (S1 : Typ) (e1 : Trm) (T : Typ),
  Typing [] (Trm.trm_abs S1 e1) T → ∀ (U1 U2 : Typ), Sub [] T (Typ.typ_all U1 U2) →
  Sub [] U1 S1 ∧ ∃ (S2 : Typ) (L : Vars), ∀ (x : Var), x ∉ L →
    Typing ([(x, S1)]) (open_e e1 (Trm.trm_fvar x)) (open_t S2 (Trm.trm_fvar x)) ∧
    Sub ([(x, U1)]) (open_t S2 (Trm.trm_fvar x)) (open_t U2 (Trm.trm_fvar x)) := by
  -- TODO
  sorry

end Lp2lc.Active.Dsub
