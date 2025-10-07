/- Dot_top_bot Proof scaffolds

This file mirrors lemmas in Coq `Lp2lc_coq/Active/Dot_top_bot.v` and provides
theorem statements with `sorry` placeholders. No axioms. Keep the original order.
-/

import Std
import «Lp2lc».Active.Dot_top_bot.Def
import «Lp2lc».Active.Dot_top_bot.Auxiliary

namespace Lp2lc.Active.Dot_top_bot

-- ######################################################################
-- Infrastructure and basic lemmas

/-- Freshness contradiction: x is never fresh in E ++ [(x, a)]. -/
@[simp] theorem fresh_push_eq_inv {A} (x : Var) (a : A) (E : List (Var × A)) :
  x ∉ Env.dom (E ++ [(x, a)]) → False := by
  intro hx
  classical
  have hx_mem : x ∈ Env.dom (E ++ [(x, a)]) := by
    -- dom (E ++ [(x,a)]) == toFinset (map fst E ++ [x])
    change x ∈ ((List.map (fun p : Var × A => p.fst) (E ++ [(x, a)])).toFinset)
    simp [List.map_append]
  exact hx hx_mem

-- ######################################################################
-- Weakening (statements only; proofs deferred)

theorem weaken_rules :
  (∀ m1 m2 G t T, ty_trm m1 m2 G t T → ∀ G1 G2 G3,
     G = G1 ++ G3 →
     Lp2lc.Active.ok (G1 ++ G2 ++ G3) →
     ty_trm m1 m2 (G1 ++ G2 ++ G3) t T) ∧
  (∀ G d D, ty_def G d D → ∀ G1 G2 G3,
     G = G1 ++ G3 →
     Lp2lc.Active.ok (G1 ++ G2 ++ G3) →
     ty_def (G1 ++ G2 ++ G3) d D) ∧
  (∀ G ds T, ty_defs G ds T → ∀ G1 G2 G3,
     G = G1 ++ G3 →
     Lp2lc.Active.ok (G1 ++ G2 ++ G3) →
     ty_defs (G1 ++ G2 ++ G3) ds T) ∧
  (∀ m1 m2 G T U, subtyp m1 m2 G T U → ∀ G1 G2 G3,
     G = G1 ++ G3 →
     Lp2lc.Active.ok (G1 ++ G2 ++ G3) →
     subtyp m1 m2 (G1 ++ G2 ++ G3) T U) := by
  -- TODO: mutual induction on typing/subtyping rules
  sorry

/-- Weakening for term typing. -/
theorem weaken_ty_trm (m1 m2) (G1 G2 : ctx) (t : trm) (T : typ) :
  ty_trm m1 m2 G1 t T →
  Lp2lc.Active.ok (G1 ++ G2) →
  ty_trm m1 m2 (G1 ++ G2) t T := by
  -- TODO: derive from weaken_rules
  sorry

/-- Weakening for subtyping. -/
theorem weaken_subtyp (m1 m2) (G1 G2 : ctx) (S U : typ) :
  subtyp m1 m2 G1 S U →
  Lp2lc.Active.ok (G1 ++ G2) →
  subtyp m1 m2 (G1 ++ G2) S U := by
  -- TODO: derive from weaken_rules
  sorry

-- ######################################################################
-- Well-formed store (statements)

theorem wf_sto_to_ok_s (s : sto) (G : ctx) :
  wf_sto G s → Lp2lc.Active.ok s := by
  -- TODO: structural induction on wf_sto
  sorry


theorem wf_sto_to_ok_G (s : sto) (G : ctx) :
  wf_sto G s → Lp2lc.Active.ok G := by
  -- TODO: structural induction on wf_sto
  sorry

-- ######################################################################
-- Store/context relation helpers (statements)

theorem ctx_binds_to_sto_binds_raw (s : sto) (G : ctx) (x : Var) (T : typ) :
  wf_sto G s →
  Env.binds x T G →
  ∃ G1 G2 v, G = G1 ++ ((x, T) :: G2) ∧ Env.binds x v s ∧ ty_trm ty_precise sub_general G1 (trm.trm_val v) T := by
  -- TODO
  sorry


theorem sto_binds_to_ctx_binds_raw (s : sto) (G : ctx) (x : Var) (v : val) :
  wf_sto G s →
  Env.binds x v s →
  ∃ G1 G2 T, G = G1 ++ ((x, T) :: G2) ∧ ty_trm ty_precise sub_general G1 (trm.trm_val v) T := by
  -- TODO
  sorry


theorem invert_wf_sto_concat (s : sto) (G1 G2 : ctx) :
  wf_sto (G1 ++ G2) s → ∃ s1 s2, s = s1 ++ s2 ∧ wf_sto G1 s1 := by
  -- TODO
  sorry


theorem sto_unbound_to_ctx_unbound (s : sto) (G : ctx) (x : Var) :
  wf_sto G s → x ∉ Env.dom s → x ∉ Env.dom G := by
  -- TODO
  sorry


theorem ctx_unbound_to_sto_unbound (s : sto) (G : ctx) (x : Var) :
  wf_sto G s → x ∉ Env.dom G → x ∉ Env.dom s := by
  -- TODO
  sorry

-- ######################################################################
-- Typing inversions (statements)

theorem typing_implies_bound (m1 m2) (G : ctx) (x : Var) (T : typ) :
  ty_trm m1 m2 G (trm.trm_var (avar.avar_f x)) T → ∃ S, Env.binds x S G := by
  -- TODO: inversion on typing
  sorry


theorem typing_bvar_implies_false (m1 m2) (G : ctx) (a : Nat) (T : typ) :
  ty_trm m1 m2 G (trm.trm_var (avar.avar_b a)) T → False := by
  -- TODO: inversion on typing
  sorry

-- ######################################################################
-- Extra Rec (statements)

theorem extra_bnd_rules :
  (∀ m1 m2 G t T, ty_trm m1 m2 G t T → ∀ G1 G2 x S G',
    G = G1 ++ ((x, open_typ x S) :: G2) →
    G' = G1 ++ ((x, typ.typ_bnd S) :: G2) →
    ty_trm m1 m2 G' t T)
  ∧ (∀ G d D, ty_def G d D → ∀ G1 G2 x S G',
    G = G1 ++ ((x, open_typ x S) :: G2) →
    G' = G1 ++ ((x, typ.typ_bnd S) :: G2) →
    ty_def G' d D)
  ∧ (∀ G ds T, ty_defs G ds T → ∀ G1 G2 x S G',
    G = G1 ++ ((x, open_typ x S) :: G2) →
    G' = G1 ++ ((x, typ.typ_bnd S) :: G2) →
    ty_defs G' ds T)
  ∧ (∀ m1 m2 G T U, subtyp m1 m2 G T U → ∀ G1 G2 x S G',
    G = G1 ++ ((x, open_typ x S) :: G2) →
    G' = G1 ++ ((x, typ.typ_bnd S) :: G2) →
    subtyp m1 m2 G' T U) := by
  -- TODO: mutual induction on typing/subtyping rules
  sorry

-- ######################################################################
-- Substitution — freshness and commuting (statements)

theorem subst_fresh_avar : ∀ (x y : Var), ∀ a : avar,
  x ∉ fv_avar a → subst_avar x y a = a := by
  -- TODO: by cases on a
  sorry

theorem subst_fresh_typ_dec : ∀ (x y : Var),
  (∀ T : typ, x ∉ fv_typ T → subst_typ x y T = T) ∧
  (∀ D : dec, x ∉ fv_dec D → subst_dec x y D = D) := by
  -- TODO: mutual structural induction
  sorry

theorem subst_fresh_trm_val_def_defs : ∀ (x y : Var),
  (∀ t : trm, x ∉ fv_trm t → subst_trm x y t = t) ∧
  (∀ v : val, x ∉ fv_val v → subst_val x y v = v) ∧
  (∀ d : defn, x ∉ fv_def d → subst_def x y d = d) ∧
  (∀ ds : defs, x ∉ fv_defs ds → subst_defs x y ds = ds) := by
  -- TODO: mutual structural induction
  sorry

theorem invert_fv_ctx_types_push : ∀ (x z : Var) (T : typ) (G : ctx),
  x ∉ fv_ctx_types ((z, T) :: G) → x ∉ fv_typ T ∧ x ∉ fv_ctx_types G := by
  -- TODO
  sorry

theorem subst_fresh_ctx : ∀ (x y : Var) (G : ctx),
  x ∉ fv_ctx_types G → subst_ctx x y G = G := by
  -- TODO: env fold + projections
  sorry

theorem subst_open_commute_avar : ∀ (x y u : Var), ∀ a : avar, ∀ n : Nat,
  subst_avar x y (open_rec_avar n u a) =
  open_rec_avar n (subst_fvar x y u) (subst_avar x y a) := by
  -- TODO
  sorry

theorem subst_open_commute_typ_dec : ∀ (x y u : Var),
  (∀ t : typ, ∀ n : Nat,
     subst_typ x y (open_rec_typ n u t) =
     open_rec_typ n (subst_fvar x y u) (subst_typ x y t)) ∧
  (∀ D : dec, ∀ n : Nat,
     subst_dec x y (open_rec_dec n u D) =
     open_rec_dec n (subst_fvar x y u) (subst_dec x y D)) := by
  -- TODO: mutual structural induction
  sorry

theorem subst_open_commute_typ : ∀ (x y u : Var) (T : typ),
  subst_typ x y (open_typ u T) = open_typ (subst_fvar x y u) (subst_typ x y T) := by
  -- TODO: from subst_open_commute_typ_dec
  sorry

theorem subst_open_commute_dec : ∀ (x y u : Var) (D : dec),
  subst_dec x y (open_dec u D) = open_dec (subst_fvar x y u) (subst_dec x y D) := by
  -- TODO: from subst_open_commute_typ_dec
  sorry

theorem subst_open_commute_trm_val_def_defs : ∀ (x y u : Var),
  (∀ t : trm, ∀ n : Nat,
     subst_trm x y (open_rec_trm n u t) =
     open_rec_trm n (subst_fvar x y u) (subst_trm x y t)) ∧
  (∀ v : val, ∀ n : Nat,
     subst_val x y (open_rec_val n u v) =
     open_rec_val n (subst_fvar x y u) (subst_val x y v)) ∧
  (∀ d : defn, ∀ n : Nat,
     subst_def x y (open_rec_def n u d) =
     open_rec_def n (subst_fvar x y u) (subst_def x y d)) ∧
  (∀ ds : defs, ∀ n : Nat,
     subst_defs x y (open_rec_defs n u ds) =
     open_rec_defs n (subst_fvar x y u) (subst_defs x y ds)) := by
  -- TODO: mutual structural induction
  sorry

theorem subst_open_commute_trm : ∀ (x y u : Var) (t : trm),
  subst_trm x y (open_trm u t) = open_trm (subst_fvar x y u) (subst_trm x y t) := by
  -- TODO: from subst_open_commute_trm_val_def_defs
  sorry

theorem subst_open_commute_val : ∀ (x y u : Var) (v : val),
  subst_val x y (open_val u v) = open_val (subst_fvar x y u) (subst_val x y v) := by
  -- TODO: from subst_open_commute_trm_val_def_defs
  sorry

theorem subst_open_commute_defs : ∀ (x y u : Var) (ds : defs),
  subst_defs x y (open_defs u ds) = open_defs (subst_fvar x y u) (subst_defs x y ds) := by
  -- TODO: from subst_open_commute_trm_val_def_defs
  sorry

-- Substitution — intro and undo (statements)

theorem subst_intro_trm : ∀ (x u : Var) (t : trm),
  x ∉ fv_trm t → open_trm u t = subst_trm x u (open_trm x t) := by
  -- TODO
  sorry

theorem subst_intro_val : ∀ (x u : Var) (v : val),
  x ∉ fv_val v → open_val u v = subst_val x u (open_val x v) := by
  -- TODO
  sorry

theorem subst_intro_defs : ∀ (x u : Var) (ds : defs),
  x ∉ fv_defs ds → open_defs u ds = subst_defs x u (open_defs x ds) := by
  -- TODO
  sorry

theorem subst_intro_typ : ∀ (x u : Var) (T : typ),
  x ∉ fv_typ T → open_typ u T = subst_typ x u (open_typ x T) := by
  -- TODO
  sorry

theorem subst_intro_dec : ∀ (x u : Var) (D : dec),
  x ∉ fv_dec D → open_dec u D = subst_dec x u (open_dec x D) := by
  -- TODO
  sorry

theorem subst_undo_avar : ∀ (x y : Var),
  (∀ a : avar, y ∉ fv_avar a → subst_avar y x (subst_avar x y a) = a) := by
  -- TODO
  sorry

theorem subst_undo_typ_dec : ∀ (x y : Var),
  (∀ T : typ, y ∉ fv_typ T → subst_typ y x (subst_typ x y T) = T) ∧
  (∀ D : dec, y ∉ fv_dec D → subst_dec y x (subst_dec x y D) = D) := by
  -- TODO
  sorry

theorem subst_undo_trm_val_def_defs : ∀ (x y : Var),
  (∀ t : trm, y ∉ fv_trm t → subst_trm y x (subst_trm x y t) = t) ∧
  (∀ v : val, y ∉ fv_val v → subst_val y x (subst_val x y v) = v) ∧
  (∀ d : defn, y ∉ fv_def d → subst_def y x (subst_def x y d) = d) ∧
  (∀ ds : defs, y ∉ fv_defs ds → subst_defs y x (subst_defs x y ds) = ds) := by
  -- TODO
  sorry

end Lp2lc.Active.Dot_top_bot
