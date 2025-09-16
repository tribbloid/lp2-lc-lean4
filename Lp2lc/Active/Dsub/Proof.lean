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
  def_type T → ∀ u k, T = open_t_rec k u T := by
  -- TODO
  sorry

theorem open_rec_lc_e : ∀ e,
  def_term e → ∀ u k, e = open_e_rec k u e := by
  -- TODO
  sorry

-- Coq line 418: Lemma open_t_var_type

theorem open_t_var_type : ∀ x T,
  def_type T → open_t T (trm.trm_fvar x) = T := by
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

theorem value_is_term : ∀ e, value e -> def_term e := by
  intro e h
  cases h with
  | value_abs V e1 hterm =>
    exact hterm
  | value_mem V hterm =>
    exact hterm

-- Coq lines 548–564: wf_lc split
-- Prove wft_type and wfe_term structurally (no mutual recursion cycle),
-- then define wf_lc_t/e as wrappers.

theorem wft_type : ∀ E T, wft E T → def_type T := by
  -- TODO
  sorry


theorem wfe_term : ∀ E e, wfe E e → def_term e := by
  -- TODO
  sorry


theorem wf_lc_t : ∀ E T, wft E T -> def_type T := by
  -- TODO
  sorry


theorem wf_lc_e : ∀ E e, wfe E e -> def_term e := by
  -- TODO
  sorry

-- Coq lines 568–613: weakening for wft/wfe

theorem wft_weaken : ∀ G T E F,
  wft (E ++ G) T → ok (E ++ F ++ G) → wft (E ++ F ++ G) T := by
  -- TODO
  sorry

theorem wfe_weaken : ∀ G e E F,
  wfe (E ++ G) e → ok (E ++ F ++ G) → wfe (E ++ F ++ G) e := by
  -- TODO
  sorry

-- Coq lines 757–764: ok_from_okt

theorem ok_from_okt : ∀ E, okt E → ok E := by
  -- TODO
  sorry

-- Coq lines 782–788: wft_from_okt (adapted)

theorem wft_from_okt : ∀ x T E, okt ((x, T) :: E) → wft E T := by
  -- TODO
  sorry

-- Coq lines 792–800: wft_weaken_right

theorem wft_weaken_right : ∀ T E F,
  wft E T → ok (E ++ F) → wft (E ++ F) T := by
  -- TODO
  sorry

-- Coq lines 939–963: regularity of sub/has and typing

theorem sub_regular : ∀ E S T,
  sub E S T → okt E ∧ wft E S ∧ wft E T := by
  -- TODO
  sorry

theorem has_regular : ∀ E p T,
  has E p T → okt E ∧ wft E (typ.typ_sel p) ∧ wft E T := by
  -- TODO
  sorry

theorem has_regular_e : ∀ E p T,
  has E p T → (value p ∨ ∃ x, trm.trm_fvar x = p) ∧ wfe E p := by
  -- TODO
  sorry

-- Coq lines 974–995: typing_regular and value_regular

theorem typing_regular : ∀ E e T,
  typing E e T → okt E ∧ wfe E e ∧ wft E T := by
  -- TODO
  sorry

theorem value_regular : ∀ t, value t → def_term t := by
  intro t h
  exact value_is_term t h

-- Coq lines 1006–1012: red_regular

theorem red_regular : ∀ t t',
  red t t' → def_term t ∧ def_term t' := by
  -- TODO
  sorry

-- Coq lines 1066–1075: sub_reflexivity

theorem sub_reflexivity : ∀ E T,
  okt E → wft E T → sub E T T := by
  -- TODO
  sorry

-- Coq lines 1080–1160: weakening for sub/has

theorem sub_weakening : ∀ E F G S T,
  sub (E ++ G) S T → okt (E ++ F ++ G) → sub (E ++ F ++ G) S T := by
  -- TODO
  sorry


theorem has_weakening : ∀ E F G p T,
  has (E ++ G) p T → okt (E ++ F ++ G) → has (E ++ F ++ G) p T := by
  -- TODO
  sorry

-- Coq lines 1334–1385: typing weakening/narrowing

theorem typing_weakening : ∀ E F G e T,
  typing (E ++ G) e T → okt (E ++ F ++ G) → typing (E ++ F ++ G) e T := by
  -- TODO
  sorry


theorem typing_narrowing : ∀ Q E F X P e T,
  sub E P Q → typing (E ++ [(X, Q)] ++ F) e T → typing (E ++ [(X, P)] ++ F) e T := by
  -- TODO
  sorry


theorem typing_narrowing_empty : ∀ Q X P e T,
  sub [] P Q → typing ([(X, Q)]) e T → typing ([(X, P)]) e T := by
  -- TODO
  sorry

-- Coq lines 1385–1414: typing through substitution

theorem typing_through_subst : ∀ U E F z T e u,
  typing (E ++ [(z, U)] ++ F) e T →
  (value u ∨ ∃ x, trm.trm_fvar x = u) → typing E u U →
  typing (E ++ map_subst_t z u F) (subst_e z u e) (subst_t z u T) := by
  -- TODO
  sorry

-- Coq lines 1685–1698: canonical forms

theorem canonical_form_abs : ∀ t U1 U2,
  value t → typing [] t (typ.typ_all U1 U2) → ∃ V e1, t = trm.trm_abs V e1 := by
  -- TODO
  sorry


theorem canonical_form_mem : ∀ t b T,
  value t → typing [] t (typ.typ_mem b T) → ∃ V, t = trm.trm_mem V := by
  -- TODO
  sorry

-- Coq lines 1699–1697 and others: typing_through_subst1

theorem typing_through_subst1 : ∀ V y v e T,
  typing ([(y, V)]) e T → value v → typing [] v V →
  typing [] (subst_e y v e) (subst_t y v T) := by
  -- TODO
  sorry

-- Coq lines 1703–1710: value_red_contra and preservation_result

theorem value_red_contra : ∀ e e', value e → red e e' → False := by
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
mutual
  theorem subst_open_rec_t : ∀ T1 t2 x u n, def_term u →
    subst_t x u (open_t_rec n t2 T1) =
    open_t_rec n (subst_e x u t2) (subst_t x u T1) := by
    intro T1 t2 x u n hu
    induction T1 generalizing n with
    | typ_top =>
        simp [open_t_rec, subst_t]
    | typ_sel t ih =>
        -- Delegate to term lemma for the embedded term
        simpa [open_t_rec, subst_t] using
          (congrArg typ.typ_sel (subst_open_rec_e (t1 := t) (t2 := t2) (x := x) (u := u) (n := n) hu))
    | typ_mem b T ih =>
        simp [open_t_rec, subst_t, ih n]
    | typ_all T1 T2 ih1 ih2 =>
        simp [open_t_rec, subst_t, ih1 n, ih2 (n+1)]

  theorem subst_open_rec_e : ∀ t1 t2 x u n, def_term u →
    subst_e x u (open_e_rec n t2 t1) =
    open_e_rec n (subst_e x u t2) (subst_e x u t1) := by
    intro t1 t2 x u n hu
    classical
    induction t1 generalizing n with
    | trm_bvar i =>
        simp [open_e_rec, subst_e]
    | trm_fvar y =>
        simp [open_e_rec, subst_e]
    | trm_abs V e1 ih =>
        have hV := subst_open_rec_t (T1 := V) (t2 := t2) (x := x) (u := u) (n := n) hu
        have hE := ih (n+1)
        simpa [open_e_rec, subst_e, hV, hE]
    | trm_mem T ih =>
        have hT := subst_open_rec_t (T1 := T) (t2 := t2) (x := x) (u := u) (n := n) hu
        simpa [open_e_rec, subst_e, hT]
    | trm_app e1 e2 ih1 ih2 =>
        have h1 := ih1 n
        have h2 := ih2 n
        simpa [open_e_rec, subst_e, h1, h2]
end

-- Coq lines 447–459
 theorem subst_t_open_t : ∀ T1 t2 x u, def_term u →
   subst_t x u (open_t T1 t2) =
   open_t (subst_t x u T1) (subst_e x u t2) := by
   intro T1 t2 x u hu
   simpa [open_t] using
     (subst_open_rec_t (T1 := T1) (t2 := t2) (x := x) (u := u) (n := 0) hu)
 
 theorem subst_e_open_e : ∀ t1 t2 x u, def_term u →
   subst_e x u (open_e t1 t2) =
   open_e (subst_e x u t1) (subst_e x u t2) := by
   intro t1 t2 x u hu
   simpa [open_e] using
     (subst_open_rec_e (t1 := t1) (t2 := t2) (x := x) (u := u) (n := 0) hu)

-- Coq lines 461–475
theorem subst_t_open_t_var : ∀ (x y : Var) (u : trm) (T : typ), y ≠ x → def_term u →
  open_t (subst_t x u T) (trm.trm_fvar y) = subst_t x u (open_t T (trm.trm_fvar y)) := by
  -- TODO
  sorry

theorem subst_e_open_e_var : ∀ (x y : Var) (u : trm) (e : trm), y ≠ x → def_term u →
  open_e (subst_e x u e) (trm.trm_fvar y) = subst_e x u (open_e e (trm.trm_fvar y)) := by
  -- TODO
  sorry

-- Coq lines 477–494
theorem subst_t_intro : ∀ x T2 u,
  x ∉ fv_t T2 → def_term u →
  open_t T2 u = subst_t x u (T2 open_t_var x) := by
  -- TODO
  sorry

theorem subst_e_intro : ∀ x t2 u,
  x ∉ fv_e t2 → def_term u →
  open_e t2 u = subst_e x u (t2 open_e_var x) := by
  -- TODO
  sorry

-- Coq lines 498–513: substitutions preserve local closure (split)
theorem subst_lc_t : ∀ T, def_type T → ∀ z u, def_term u → def_type (subst_t z u T) := by
  -- TODO
  sorry

theorem subst_lc_e : ∀ e, def_term e → ∀ z u, def_term u → def_term (subst_e z u e) := by
  -- TODO
  sorry

-- Coq lines 508–534: corollaries
theorem subst_e_value : ∀ e1 z e2,
  value e1 → def_term e2 → value (subst_e z e2 e1) := by
  -- TODO
  sorry

-- Coq lines 875–934: notin_fv lemmas and map_subst identity
theorem notin_fv_open_rec_t : ∀ T k y x,
  x ∉ fv_t (open_t_rec k (trm.trm_fvar y) T) → x ∉ fv_t T := by
  -- TODO
  sorry

theorem notin_fv_open_rec_e : ∀ e k y x,
  x ∉ fv_e (open_e_rec k (trm.trm_fvar y) e) → x ∉ fv_e e := by
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

theorem notin_fv_wf_t : ∀ E T, wft E T → ∀ x, x ∉ dom E → x ∉ fv_t T := by
  -- TODO
  sorry

theorem notin_fv_wf_e : ∀ E e, wfe E e → ∀ x, x ∉ dom E → x ∉ fv_e e := by
  -- TODO
  sorry

theorem notin_fv_wf : ∀ E x T,
  wft E T → x ∉ dom E → x ∉ fv_t T := by
  -- TODO
  sorry

theorem map_subst_t_id : ∀ G z u,
  okt G → z ∉ dom G → G = map_subst_t z u G := by
  -- TODO
  sorry

-- Coq lines 755–873: environment lemmas
theorem binds_weaken : ∀ (x : Var) (T : typ) (E F G : env),
  List.lookup x (E ++ G) = some T → List.lookup x (E ++ F ++ G) = some T := by
  -- TODO
  sorry

theorem wft_weaken_empty : ∀ T E,
  wft [] T → ok E → wft E T := by
  -- TODO
  sorry

theorem wfe_weaken_empty : ∀ e E,
  wfe [] e → ok E → wfe E e := by
  -- TODO
  sorry

theorem wf_narrow_t : ∀ E0 T, wft E0 T → ∀ V F U E x,
  E0 = (E ++ [(x, V)] ++ F) → ok (E ++ [(x, U)] ++ F) → wft (E ++ [(x, U)] ++ F) T := by
  -- TODO
  sorry

theorem wf_narrow_e : ∀ E0 e, wfe E0 e → ∀ V F U E x,
  E0 = (E ++ [(x, V)] ++ F) → ok (E ++ [(x, U)] ++ F) → wfe (E ++ [(x, U)] ++ F) e := by
  -- TODO
  sorry

theorem wft_narrow : ∀ V F U T E x,
  wft (E ++ [(x, V)] ++ F) T → ok (E ++ [(x, U)] ++ F) → wft (E ++ [(x, U)] ++ F) T := by
  -- TODO
  sorry

theorem wf_subst_t : ∀ E0 T, wft E0 T → ∀ F Q E Z u,
  E0 = E ++ [(Z, Q)] ++ F → (value u ∨ ∃ x, trm.trm_fvar x = u) → wfe E u →
  ok (E ++ map_subst_t Z u F) → wft (E ++ map_subst_t Z u F) (subst_t Z u T) := by
  -- TODO
  sorry

theorem wf_subst_e : ∀ E0 e, wfe E0 e → ∀ F Q E Z u,
  E0 = E ++ [(Z, Q)] ++ F → (value u ∨ ∃ x, trm.trm_fvar x = u) → wfe E u →
  ok (E ++ map_subst_t Z u F) → wfe (E ++ map_subst_t Z u F) (subst_e Z u e) := by
  -- TODO
  sorry

theorem wft_subst : ∀ F Q E Z u T,
  wft (E ++ [(Z, Q)] ++ F) T → (value u ∨ ∃ x, trm.trm_fvar x = u) → wfe E u →
  ok (E ++ map_subst_t Z u F) → wft (E ++ map_subst_t Z u F) (subst_t Z u T) := by
  -- TODO
  sorry

theorem wft_subst1 : ∀ F Q Z u T,
  wft ([(Z, Q)] ++ F) T → (value u ∨ ∃ x, trm.trm_fvar x = u) → wfe [] u →
  ok (map_subst_t Z u F) → wft (map_subst_t Z u F) (subst_t Z u T) := by
  -- TODO
  sorry

theorem wft_subst_empty : ∀ Q Z u T,
  wft ([(Z, Q)]) T → (value u ∨ ∃ x, trm.trm_fvar x = u) → wfe [] u →
  wft [] (subst_t Z u T) := by
  -- TODO
  sorry

theorem wft_open : ∀ E u T1 T2,
  ok E → wft E (typ.typ_all T1 T2) → (value u ∨ ∃ x, trm.trm_fvar x = u) → wfe E u →
  wft E (open_t T2 u) := by
  -- TODO
  sorry

-- Coq lines 805–873: okt lemmas
theorem okt_push_inv : ∀ E x T,
  okt ((x, T) :: E) → okt E ∧ wft E T ∧ E.lookup x = none := by
  -- TODO
  sorry

theorem okt_push_type : ∀ E x T,
  okt ((x, T) :: E) → def_type T := by
  -- TODO
  sorry

theorem okt_narrow : ∀ V (E F : env) U x,
  okt (E ++ [(x, V)] ++ F) → wft E U → okt (E ++ [(x, U)] ++ F) := by
  -- TODO
  sorry

theorem okt_strengthen : ∀ x T E F,
  okt (E ++ [(x, T)] ++ F) → okt (E ++ F) := by
  -- TODO
  sorry

theorem okt_subst : ∀ Q Z u (E F : env),
  okt (E ++ [(Z, Q)] ++ F) → (value u ∨ ∃ x, trm.trm_fvar x = u) → wfe E u →
  okt (E ++ map_subst_t Z u F) := by
  -- TODO
  sorry

theorem okt_subst1 : ∀ Q Z u (F : env),
  okt ([(Z, Q)] ++ F) → (value u ∨ ∃ x, trm.trm_fvar x = u) → wfe [] u →
  okt (map_subst_t Z u F) := by
  -- TODO
  sorry

-- Coq lines 1080–1160 variants: weakening 1/empty and has

theorem sub_weakening1 : ∀ E F G S T,
  sub E S T → okt (E ++ F ++ G) → sub (E ++ F ++ G) S T := by
  -- TODO
  sorry

theorem sub_weakening_empty : ∀ E S T,
  sub [] S T → okt E → sub E S T := by
  -- TODO
  sorry

theorem has_weakening1 : ∀ E F G p T,
  has E p T → okt (E ++ F ++ G) → has (E ++ F ++ G) p T := by
  -- TODO
  sorry

theorem has_weakening_empty : ∀ E p T,
  has [] p T → okt E → has E p T := by
  -- TODO
  sorry

-- Coq lines 1178–1234: Narrowing and transitivity
theorem sub_has_narrowing_aux_t : ∀ E0 S T, sub E0 S T → ∀ Q E F z P,
  E0 = (E ++ [(z, Q)] ++ F) → sub E P Q → sub (E ++ [(z, P)] ++ F) S T := by
  -- TODO
  sorry

theorem sub_has_narrowing_aux_e : ∀ E0 p T, has E0 p T → ∀ Q E F z P,
  E0 = (E ++ [(z, Q)] ++ F) → sub E P Q → has (E ++ [(z, P)] ++ F) p T := by
  -- TODO
  sorry

theorem sub_narrowing : ∀ Q E F z P S T,
  sub E P Q → sub (E ++ [(z, Q)] ++ F) S T → sub (E ++ [(z, P)] ++ F) S T := by
  -- TODO
  sorry

theorem sub_narrowing_empty : ∀ Q z P S T,
  sub [] P Q → sub ([(z, Q)]) S T → sub ([(z, P)]) S T := by
  -- TODO
  sorry

-- Coq lines 1240–1326: substitution preserves subtyping
theorem has_value_var : ∀ E u T,
  has E u T → (value u ∨ ∃ x, trm.trm_fvar x = u) := by
  -- TODO
  sorry

theorem var_typing_has : ∀ E x Q,
  typing E (trm.trm_fvar x) Q → has E (trm.trm_fvar x) Q := by
  -- TODO
  sorry

theorem val_typing_has : ∀ E u Q,
  value u → typing E u Q → has E u Q := by
  -- TODO
  sorry

theorem sub_has_through_subst_t : ∀ E0 S T, sub E0 S T → ∀ Q E F Z u,
  E0 = (E ++ [(Z, Q)] ++ F) → (value u ∨ ∃ x, trm.trm_fvar x = u) → typing E u Q →
  sub (E ++ map_subst_t Z u F) (subst_t Z u S) (subst_t Z u T) := by
  -- TODO
  sorry

theorem sub_has_through_subst_e : ∀ E0 p T, has E0 p T → ∀ Q E F Z u,
  E0 = (E ++ [(Z, Q)] ++ F) → (value u ∨ ∃ x, trm.trm_fvar x = u) → typing E u Q →
  has (E ++ map_subst_t Z u F) (subst_e Z u p) (subst_t Z u T) := by
  -- TODO
  sorry

-- Coq lines 1453–1663: psub and possible_types lemmas
theorem has_empty_value : ∀ p T,
  has [] p T → value p := by
  -- TODO
  sorry

theorem psub_sub : ∀ S T,
  psub S T → sub [] S T := by
  -- TODO
  sorry

theorem possible_types_value : ∀ n p T,
  possible_types n p T → value p := by
  -- TODO
  sorry

theorem possible_types_wfe : ∀ n p T,
  possible_types n p T → wfe [] p := by
  -- TODO
  sorry

theorem possible_types_wft : ∀ n p T,
  possible_types n p T → wft [] T := by
  -- TODO
  sorry

theorem has_empty_var_false : ∀ x T,
  has [] (trm.trm_fvar x) T → False := by
  -- TODO
  sorry

theorem possible_types_closure_psub : ∀ n v T U,
  possible_types n v T → psub T U → possible_types n v U := by
  -- TODO
  sorry

theorem psub_reflexivity : ∀ T,
  wft [] T → psub T T := by
  -- TODO
  sorry

theorem sub_psub_aux_t : ∀ E S T, sub E S T → E = [] → psub S T := by
  -- TODO
  sorry

theorem sub_psub_aux_e : ∀ E p T, has E p T → E = [] → possible_types 0 p T := by
  -- TODO
  sorry

theorem sub_psub : ∀ S T,
  sub [] S T → psub S T := by
  -- TODO
  sorry

theorem possible_types_closure : ∀ n v T U,
  possible_types n v T → sub [] T U → possible_types n v U := by
  -- TODO
  sorry

theorem possible_types_typing : ∀ v T,
  typing [] v T → value v → possible_types 1 v T := by
  -- TODO
  sorry

theorem typing_inv_abs : ∀ (S1 : typ) (e1 : trm) (T : typ),
  typing [] (trm.trm_abs S1 e1) T → ∀ (U1 U2 : typ), sub [] T (typ.typ_all U1 U2) →
  sub [] U1 S1 ∧ ∃ (S2 : typ) (L : Vars), ∀ (x : Var), x ∉ L →
    typing ([(x, S1)]) (open_e e1 (trm.trm_fvar x)) (open_t S2 (trm.trm_fvar x)) ∧
    sub ([(x, U1)]) (open_t S2 (trm.trm_fvar x)) (open_t U2 (trm.trm_fvar x)) := by
  -- TODO
  sorry

end Lp2lc.Active.Dsub
