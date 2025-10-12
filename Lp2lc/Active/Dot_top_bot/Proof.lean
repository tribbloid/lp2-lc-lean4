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

-- Further substitution lemmas (undo/idempotence) and label invariants

theorem subst_typ_undo (x y : Var) (T : typ) :
  y ∉ fv_typ T → subst_typ y x (subst_typ x y T) = T := by
  -- TODO
  sorry

theorem subst_trm_undo (x y : Var) (t : trm) :
  y ∉ fv_trm t → subst_trm y x (subst_trm x y t) = t := by
  -- TODO
  sorry

theorem subst_idempotent_avar (x y : Var) :
  (∀ a : avar, subst_avar x y (subst_avar x y a) = subst_avar x y a) := by
  -- TODO
  sorry

theorem subst_idempotent_typ_dec (x y : Var) :
  (∀ T : typ, subst_typ x y (subst_typ x y T) = subst_typ x y T) ∧
  (∀ D : dec, subst_dec x y (subst_dec x y D) = subst_dec x y D) := by
  -- TODO
  sorry

theorem subst_idempotent_trm_val_def_defs (x y : Var) :
  (∀ t : trm, subst_trm x y (subst_trm x y t) = subst_trm x y t) ∧
  (∀ v : val, subst_val x y (subst_val x y v) = subst_val x y v) ∧
  (∀ d : defn, subst_def x y (subst_def x y d) = subst_def x y d) ∧
  (∀ ds : defs, subst_defs x y (subst_defs x y ds) = subst_defs x y ds) := by
  -- TODO
  sorry

theorem subst_typ_idempotent (x y : Var) (T : typ) :
  subst_typ x y (subst_typ x y T) = subst_typ x y T := by
  -- TODO
  sorry

theorem subst_trm_idempotent (x y : Var) (t : trm) :
  subst_trm x y (subst_trm x y t) = subst_trm x y t := by
  -- TODO
  sorry

theorem subst_label_of_dec (x y : Var) (D : dec) :
  label_of_dec D = label_of_dec (subst_dec x y D) := by
  -- TODO
  sorry

theorem subst_label_of_def (x y : Var) (d : defn) :
  label_of_def d = label_of_def (subst_def x y d) := by
  -- TODO
  sorry

theorem subst_defs_hasnt (x y : Var) (l : label) (ds : defs) :
  defs_hasnt ds l → defs_hasnt (subst_defs x y ds) l := by
  -- TODO
  sorry

-- ######################################################################
-- Substitution principle (statements)

theorem subst_rules (y : Var) (S : typ) :
  (∀ m1 m2 G t T, ty_trm m1 m2 G t T → ∀ G1 G2 x,
     G = G1 ++ ((x, S) :: G2) →
     Lp2lc.Active.ok (G1 ++ ((x, S) :: G2)) →
     y ∉ fv_ctx_types G1 →
     ty_trm ty_general sub_general (G1 ++ subst_ctx x y G2) (trm.trm_var (avar.avar_f y)) (subst_typ x y S) →
     m1 = ty_general → m2 = sub_general →
     ty_trm m1 m2 (G1 ++ subst_ctx x y G2) (subst_trm x y t) (subst_typ x y T)) ∧
  (∀ G d D, ty_def G d D → ∀ G1 G2 x,
     G = G1 ++ ((x, S) :: G2) →
     Lp2lc.Active.ok (G1 ++ ((x, S) :: G2)) →
     y ∉ fv_ctx_types G1 →
     ty_trm ty_general sub_general (G1 ++ subst_ctx x y G2) (trm.trm_var (avar.avar_f y)) (subst_typ x y S) →
     ty_def (G1 ++ subst_ctx x y G2) (subst_def x y d) (subst_dec x y D)) ∧
  (∀ G ds T, ty_defs G ds T → ∀ G1 G2 x,
     G = G1 ++ ((x, S) :: G2) →
     Lp2lc.Active.ok (G1 ++ ((x, S) :: G2)) →
     y ∉ fv_ctx_types G1 →
     ty_trm ty_general sub_general (G1 ++ subst_ctx x y G2) (trm.trm_var (avar.avar_f y)) (subst_typ x y S) →
     ty_defs (G1 ++ subst_ctx x y G2) (subst_defs x y ds) (subst_typ x y T)) ∧
  (∀ m1 m2 G T U, subtyp m1 m2 G T U → ∀ G1 G2 x,
     G = G1 ++ ((x, S) :: G2) →
     Lp2lc.Active.ok (G1 ++ ((x, S) :: G2)) →
     y ∉ fv_ctx_types G1 →
     ty_trm ty_general sub_general (G1 ++ subst_ctx x y G2) (trm.trm_var (avar.avar_f y)) (subst_typ x y S) →
     m1 = ty_general → m2 = sub_general →
     subtyp m1 m2 (G1 ++ subst_ctx x y G2) (subst_typ x y T) (subst_typ x y U)) := by
  -- TODO
  sorry

theorem subst_ty_trm (y : Var) (S : typ) (G : ctx) (x : Var) (t : trm) (T : typ) :
  ty_trm ty_general sub_general (G ++ [(x, S)]) t T →
  Lp2lc.Active.ok (G ++ [(x, S)]) →
  y ∉ fv_ctx_types G →
  ty_trm ty_general sub_general G (trm.trm_var (avar.avar_f y)) (subst_typ x y S) →
  ty_trm ty_general sub_general G (subst_trm x y t) (subst_typ x y T) := by
  -- TODO
  sorry

theorem subst_ty_defs (y : Var) (S : typ) (G : ctx) (x : Var) (ds : defs) (T : typ) :
  ty_defs (G ++ [(x, S)]) ds T →
  Lp2lc.Active.ok (G ++ [(x, S)]) →
  y ∉ fv_ctx_types G →
  ty_trm ty_general sub_general G (trm.trm_var (avar.avar_f y)) (subst_typ x y S) →
  ty_defs G (subst_defs x y ds) (subst_typ x y T) := by
  -- TODO
  sorry

-- ######################################################################
-- Some lemmas (statements)

theorem corresponding_types (G : ctx) (s : sto) (x : Var) (T : typ) :
  wf_sto G s → Env.binds x T G →
  ((∃ S U t, Env.binds x (val.val_lambda S t) s ∧
             ty_trm ty_precise sub_general G (trm.trm_val (val.val_lambda S t)) (typ.typ_all S U) ∧
             T = typ.typ_all S U)
   ∨ (∃ S ds, Env.binds x (val.val_new S ds) s ∧
              ty_trm ty_precise sub_general G (trm.trm_val (val.val_new S ds)) (typ.typ_bnd S) ∧
              T = typ.typ_bnd S)) := by
  -- TODO
  sorry

theorem unique_rec_subtyping (G : ctx) (S T : typ) :
  subtyp ty_precise sub_general G (typ.typ_bnd S) T → T = typ.typ_bnd S := by
  -- TODO
  sorry

theorem unique_all_subtyping (G : ctx) (S U T : typ) :
  subtyp ty_precise sub_general G (typ.typ_all S U) T → T = typ.typ_all S U := by
  -- TODO
  sorry

theorem unique_lambda_typing (G : ctx) (x : Var) (S U T : typ) :
  Env.binds x (typ.typ_all S U) G →
  ty_trm ty_precise sub_general G (trm.trm_var (avar.avar_f x)) T →
  T = typ.typ_all S U := by
  -- TODO
  sorry

theorem lambda_not_rcd (G : ctx) (x : Var) (S U : typ) (A : typ_label) (T : typ) :
  Env.binds x (typ.typ_all S U) G →
  ty_trm ty_precise sub_general G (trm.trm_var (avar.avar_f x)) (typ.typ_rcd (dec.dec_typ A T T)) → False := by
  -- TODO
  sorry

-- Record opening/label preservation

theorem open_dec_preserves_label (D : dec) (x : Var) (i : Nat) :
  label_of_dec D = label_of_dec (open_rec_dec i x D) := by
  -- TODO
  sorry

theorem open_record_dec (D : dec) (x : Var) :
  record_dec D → record_dec (open_dec x D) := by
  -- TODO
  sorry

theorem open_record_typ (T : typ) (x : Var) (ls : Finset label) :
  record_typ T ls → record_typ (open_typ x T) ls := by
  -- TODO
  sorry

theorem open_eq_avar (x : Var) (i : Nat) (a1 a2 : avar) :
  x ∉ fv_avar a1 → x ∉ fv_avar a2 →
  open_rec_avar i x a1 = open_rec_avar i x a2 → a1 = a2 := by
  -- TODO
  sorry

theorem open_eq_typ_dec (x : Var) :
  (∀ T1 : typ, x ∉ fv_typ T1 → ∀ T2 : typ, x ∉ fv_typ T2 → ∀ i : Nat,
     open_rec_typ i x T1 = open_rec_typ i x T2 → T1 = T2) ∧
  (∀ D1 : dec, x ∉ fv_dec D1 → ∀ D2 : dec, x ∉ fv_dec D2 → ∀ i : Nat,
     open_rec_dec i x D1 = open_rec_dec i x D2 → D1 = D2) := by
  -- TODO
  sorry

theorem open_eq_typ (x : Var) (i : Nat) (T1 T2 : typ) :
  x ∉ fv_typ T1 → x ∉ fv_typ T2 →
  open_rec_typ i x T1 = open_rec_typ i x T2 → T1 = T2 := by
  -- TODO
  sorry

theorem open_record_dec_rev (D : dec) (x : Var) :
  x ∉ fv_dec D → record_dec (open_dec x D) → record_dec D := by
  -- TODO
  sorry

theorem open_record_typ_rev (T : typ) (x : Var) (ls : Finset label) :
  x ∉ fv_typ T → record_typ (open_typ x T) ls → record_typ T ls := by
  -- TODO
  sorry

theorem open_record_type (T : typ) (x : Var) :
  record_type T → record_type (open_typ x T) := by
  -- TODO
  sorry

theorem open_record_type_rev (T : typ) (x : Var) :
  x ∉ fv_typ T → record_type (open_typ x T) → record_type T := by
  -- TODO
  sorry

theorem label_same_typing (G : ctx) (d : defn) (D : dec) :
  ty_def G d D → label_of_def d = label_of_dec D := by
  -- TODO
  sorry

theorem record_defs_typing_rec (G : ctx) (ds : defs) (S : typ) :
  ty_defs G ds S → ∃ ls, record_typ S ls ∧ ∀ l, l ∉ ls ↔ defs_hasnt ds l := by
  -- TODO
  sorry

theorem record_defs_typing (G : ctx) (ds : defs) (S : typ) :
  ty_defs G ds S → record_type S := by
  -- TODO
  sorry

theorem record_new_typing (G : ctx) (S : typ) (ds : defs) :
  ty_trm ty_precise sub_general G (trm.trm_val (val.val_new S ds)) (typ.typ_bnd S) →
  record_type S := by
  -- TODO
  sorry

-- ######################################################################
-- Narrowing (statements)

def subenv_def := subenv -- local alias to emphasize usage

theorem subenv_push (G G' : ctx) (x : Var) (T : typ) :
  subenv_def G' G → Lp2lc.Active.ok ((x, T) :: G') → subenv_def ((x, T) :: G') ((x, T) :: G) := by
  -- TODO
  sorry

theorem subenv_last (G : ctx) (x : Var) (S U : typ) :
  subtyp ty_general sub_general G S U → Lp2lc.Active.ok (G ++ [(x, S)]) → subenv_def (G ++ [(x, S)]) (G ++ [(x, U)]) := by
  -- TODO
  sorry

theorem narrow_rules :
  (∀ m1 m2 G t T, ty_trm m1 m2 G t T → ∀ G',
     m1 = ty_general → m2 = sub_general → Lp2lc.Active.ok G' → subenv_def G' G → ty_trm m1 m2 G' t T) ∧
  (∀ G d D, ty_def G d D → ∀ G', Lp2lc.Active.ok G' → subenv_def G' G → ty_def G' d D) ∧
  (∀ G ds T, ty_defs G ds T → ∀ G', Lp2lc.Active.ok G' → subenv_def G' G → ty_defs G' ds T) ∧
  (∀ m1 m2 G S U, subtyp m1 m2 G S U → ∀ G',
     m1 = ty_general → m2 = sub_general → Lp2lc.Active.ok G' → subenv_def G' G → subtyp m1 m2 G' S U) := by
  -- TODO
  sorry

theorem narrow_typing (G G' : ctx) (t : trm) (T : typ) :
  ty_trm ty_general sub_general G t T → subenv_def G' G → Lp2lc.Active.ok G' → ty_trm ty_general sub_general G' t T := by
  -- TODO
  sorry

theorem narrow_subtyping (G G' : ctx) (S U : typ) :
  subtyp ty_general sub_general G S U → subenv_def G' G → Lp2lc.Active.ok G' → subtyp ty_general sub_general G' S U := by
  -- TODO
  sorry

-- ######################################################################
-- Has-member inversions and helpers (statements)

theorem has_member_rules_inv (G : ctx) (x : Var) (T : typ) (A : typ_label) (S U : typ) :
  has_member_rules G x T A S U →
  (T = typ.typ_rcd (dec.dec_typ A S U)) ∨
  (∃ T1 T2, T = typ.typ_and T1 T2 ∧ (has_member G x T1 A S U ∨ has_member G x T2 A S U)) ∨
  (∃ T', T = typ.typ_bnd T' ∧ has_member G x (open_typ x T') A S U) ∨
  (∃ y B T', T = typ.typ_sel (avar.avar_f y) B ∧
     ty_trm ty_precise sub_general G (trm.trm_var (avar.avar_f y)) (typ.typ_rcd (dec.dec_typ B T' T')) ∧
     has_member G x T' A S U) ∨
  (T = typ.typ_bot) := by
  -- TODO
  sorry

theorem has_member_inv (G : ctx) (x : Var) (T : typ) (A : typ_label) (S U : typ) :
  has_member G x T A S U →
  (T = typ.typ_rcd (dec.dec_typ A S U)) ∨
  (∃ T1 T2, T = typ.typ_and T1 T2 ∧ (has_member G x T1 A S U ∨ has_member G x T2 A S U)) ∨
  (∃ T', T = typ.typ_bnd T' ∧ has_member G x (open_typ x T') A S U) ∨
  (∃ y B T', T = typ.typ_sel (avar.avar_f y) B ∧
     ty_trm ty_precise sub_general G (trm.trm_var (avar.avar_f y)) (typ.typ_rcd (dec.dec_typ B T' T')) ∧
     has_member G x T' A S U) ∨
  (T = typ.typ_bot) := by
  -- TODO
  sorry

theorem has_member_covariance (G : ctx) (s : sto) (T1 T2 : typ) (x : Var)
    (A : typ_label) (S2 U2 : typ) :
  wf_sto G s →
  subtyp ty_general sub_tight G T1 T2 →
  ty_trm ty_general sub_tight G (trm.trm_var (avar.avar_f x)) T1 →
  has_member G x T2 A S2 U2 →
  ∃ S1 U1, has_member G x T1 A S1 U1 ∧
           subtyp ty_general sub_tight G S2 S1 ∧
           subtyp ty_general sub_tight G U1 U2 := by
  -- TODO
  sorry

theorem has_member_monotonicity (G : ctx) (s : sto) (x : Var) (T0 : typ) (ds : defs)
    (T : typ) (A : typ_label) (S U : typ) :
  wf_sto G s →
  Env.binds x (val.val_new T0 ds) s →
  has_member G x T A S U →
  ∃ T1, has_member G x (typ.typ_bnd T0) A T1 T1 ∧
        subtyp ty_general sub_tight G S T1 ∧
        subtyp ty_general sub_tight G T1 U := by
  -- TODO
  sorry

-- ######################################################################
-- Mode conversions and store-context relations (derived)

theorem precise_to_general :
  (∀ m1 m2 G t T, ty_trm m1 m2 G t T → m1 = ty_precise → m2 = sub_general → ty_trm ty_general sub_general G t T) ∧
  (∀ m1 m2 G S U, subtyp m1 m2 G S U → m1 = ty_precise → m2 = sub_general → subtyp ty_general sub_general G S U) := by
  -- TODO
  sorry

theorem precise_to_general_typing (G : ctx) (t : trm) (T : typ) :
  ty_trm ty_precise sub_general G t T → ty_trm ty_general sub_general G t T := by
  -- TODO
  sorry

theorem tight_to_general :
  (∀ m1 m2 G t T, ty_trm m1 m2 G t T → m1 = ty_general → m2 = sub_tight → ty_trm ty_general sub_general G t T) ∧
  (∀ m1 m2 G S U, subtyp m1 m2 G S U → m1 = ty_general → m2 = sub_tight → subtyp ty_general sub_general G S U) := by
  -- TODO
  sorry

theorem tight_to_general_typing (G : ctx) (t : trm) (T : typ) :
  ty_trm ty_general sub_tight G t T → ty_trm ty_general sub_general G t T := by
  -- TODO
  sorry

theorem tight_to_general_subtyping (G : ctx) (S U : typ) :
  subtyp ty_general sub_tight G S U → subtyp ty_general sub_general G S U := by
  -- TODO
  sorry

theorem precise_to_tight :
  (∀ m1 m2 G t T, ty_trm m1 m2 G t T → m1 = ty_precise → m2 = sub_general → ty_trm ty_general sub_tight G t T) ∧
  (∀ m1 m2 G S U, subtyp m1 m2 G S U → m1 = ty_precise → m2 = sub_general → subtyp ty_general sub_tight G S U) := by
  -- TODO
  sorry

theorem precise_to_tight_typing (G : ctx) (t : trm) (T : typ) :
  ty_trm ty_precise sub_general G t T → ty_trm ty_general sub_tight G t T := by
  -- TODO
  sorry

theorem general_to_tight (G0 : ctx) (s0 : sto) :
  wf_sto G0 s0 →
  (∀ m1 m2 G t T, ty_trm m1 m2 G t T → G = G0 → m1 = ty_general → m2 = sub_general → ty_trm ty_general sub_tight G t T) ∧
  (∀ m1 m2 G S U, subtyp m1 m2 G S U → G = G0 → m1 = ty_general → m2 = sub_general → subtyp ty_general sub_tight G S U) := by
  -- TODO
  sorry

theorem general_to_tight_subtyping (G : ctx) (s : sto) (S U : typ) :
  wf_sto G s → subtyp ty_general sub_general G S U → subtyp ty_general sub_tight G S U := by
  -- TODO
  sorry

theorem sto_binds_to_ctx_binds (G : ctx) (s : sto) (x : Var) (v : val) :
  wf_sto G s → Env.binds x v s → ∃ S, Env.binds x S G := by
  -- TODO
  sorry

theorem ctx_binds_to_sto_binds (G : ctx) (s : sto) (x : Var) (T : typ) :
  wf_sto G s → Env.binds x T G → ∃ v, Env.binds x v s := by
  -- TODO
  sorry

theorem val_new_typing (G : ctx) (s : sto) (x : Var) (T : typ) (ds : defs) :
  wf_sto G s → Env.binds x (val.val_new T ds) s →
  ty_trm ty_precise sub_general G (trm.trm_val (val.val_new T ds)) (typ.typ_bnd T) := by
  -- TODO
  sorry

-- ######################################################################
-- Record-sub lemmas (statements)

theorem record_typ_sub_closed (T T' : typ) (ls : Finset label) :
  record_sub T T' → record_typ T ls → ∃ ls', record_typ T' ls' ∧ ls' ⊆ ls := by
  -- TODO
  sorry

theorem record_type_sub_closed (T T' : typ) :
  record_sub T T' → record_type T → record_type T' := by
  -- TODO
  sorry

theorem record_sub_trans (T1 T2 T3 : typ) :
  record_sub T1 T2 → record_sub T2 T3 → record_sub T1 T3 := by
  -- TODO
  sorry

theorem record_subtyping (G : ctx) (T T' : typ) :
  subtyp ty_precise sub_general G T T' → record_type T → record_sub T T' := by
  -- TODO
  sorry

theorem record_typ_sub_label_in (T : typ) (D : dec) (ls : Finset label) :
  record_typ T ls → record_sub T (typ.typ_rcd D) → label_of_dec D ∈ ls := by
  -- TODO
  sorry

theorem rcd_typ_eq_bounds (T : typ) (A : typ_label) (S U : typ) :
  record_type T → record_sub T (typ.typ_rcd (dec.dec_typ A S U)) → S = U := by
  -- TODO
  sorry

theorem unique_rcd_typ (T : typ) (A : typ_label) (T1 T2 : typ) :
  record_type T →
  record_sub T (typ.typ_rcd (dec.dec_typ A T1 T1)) →
  record_sub T (typ.typ_rcd (dec.dec_typ A T2 T2)) →
  T1 = T2 := by
  -- TODO
  sorry

theorem record_type_sub_not_rec (S T : typ) (x : Var) :
  record_sub (open_typ x S) (typ.typ_bnd T) → record_type S → False := by
  -- TODO
  sorry

theorem shape_new_typing (G : ctx) (x : Var) (S T : typ) :
  Env.binds x (typ.typ_bnd S) G → record_type S →
  ty_trm ty_precise sub_general G (trm.trm_var (avar.avar_f x)) T →
  T = typ.typ_bnd S ∨ record_sub (open_typ x S) T := by
  -- TODO
  sorry

theorem unique_tight_bounds (G : ctx) (s : sto) (x : Var) (T1 T2 : typ) (A : typ_label) :
  wf_sto G s →
  ty_trm ty_precise sub_general G (trm.trm_var (avar.avar_f x)) (typ.typ_rcd (dec.dec_typ A T1 T1)) →
  ty_trm ty_precise sub_general G (trm.trm_var (avar.avar_f x)) (typ.typ_rcd (dec.dec_typ A T2 T2)) →
  T1 = T2 := by
  -- TODO
  sorry

-- ######################################################################
-- More record/has-member lemmas and possible types (statements)

theorem record_type_new (G : ctx) (s : sto) (x : Var) (T : typ) (ds : defs) :
  wf_sto G s → Env.binds x (val.val_new T ds) s → record_type (open_typ x T) := by
  -- TODO
  sorry

theorem has_member_rcd_typ_sub2_mut :
  ((∀ G x T A S U, has_member G x T A S U → record_type T →
      (T = (typ.typ_rcd (dec.dec_typ A S U)) ∨ subtyp ty_precise sub_general G T (typ.typ_rcd (dec.dec_typ A S U)))) ∧
   (∀ G x T A S U, has_member_rules G x T A S U → record_type T →
      (T = (typ.typ_rcd (dec.dec_typ A S U)) ∨ subtyp ty_precise sub_general G T (typ.typ_rcd (dec.dec_typ A S U))))) := by
  -- TODO
  sorry

theorem wf_sto_val_new_in_G (G : ctx) (s : sto) (x : Var) (T : typ) (ds : defs) :
  wf_sto G s → Env.binds x (val.val_new T ds) s → Env.binds x (typ.typ_bnd T) G := by
  -- TODO
  sorry

theorem tight_bound_completeness (G : ctx) (s : sto) (x : Var) (T : typ) (ds : defs)
    (A : typ_label) (S U : typ) :
  wf_sto G s → Env.binds x (val.val_new T ds) s →
  ty_trm ty_general sub_tight G (trm.trm_var (avar.avar_f x)) (typ.typ_rcd (dec.dec_typ A S U)) →
  subtyp ty_general sub_tight G (typ.typ_sel (avar.avar_f x) A) U ∧
  subtyp ty_general sub_tight G S (typ.typ_sel (avar.avar_f x) A) := by
  -- TODO
  sorry

theorem all_intro_inversion (G : ctx) (S : typ) (t : trm) (U : typ) :
  ty_trm ty_precise sub_general G (trm.trm_val (val.val_lambda S t)) U → ∃ T, U = typ.typ_all S T := by
  -- TODO
  sorry

theorem new_intro_inversion (G : ctx) (T : typ) (ds : defs) (U : typ) :
  ty_trm ty_precise sub_general G (trm.trm_val (val.val_new T ds)) U →
  U = typ.typ_bnd T ∧ record_type T := by
  -- TODO
  sorry

-- Possible types closure (tight)

theorem possible_types_closure_tight (G : ctx) (s : sto) (x : Var) (v : val) (T0 U0 : typ) :
  wf_sto G s → Env.binds x v s → possible_types G x v T0 →
  subtyp ty_general sub_tight G T0 U0 → possible_types G x v U0 := by
  -- TODO
  sorry

-- Pieces and inversions for possible types

theorem ty_defs_has (G : ctx) (ds : defs) (T : typ) (d : defn) :
  ty_defs G ds T → defs_has ds d → record_type T → ∃ D, ty_def G d D ∧ record_sub T (typ.typ_rcd D) := by
  -- TODO
  sorry

theorem defs_has_hasnt_neq (ds : defs) (d1 d2 : defn) :
  defs_has ds d1 → defs_hasnt ds (label_of_def d2) → label_of_def d1 ≠ label_of_def d2 := by
  -- TODO
  sorry

theorem record_has_ty_defs (G : ctx) (T : typ) (ds : defs) (D : dec) :
  ty_defs G ds T → record_has T D → ∃ d, defs_has ds d ∧ ty_def G d D := by
  -- TODO
  sorry

theorem pt_piece_rcd (G : ctx) (s : sto) (x : Var) (T : typ) (ds : defs) (d : defn) (D : dec) :
  wf_sto G s → Env.binds x (val.val_new T ds) s → defs_has (open_defs x ds) d → ty_def G d D →
  possible_types G x (val.val_new T ds) (typ.typ_rcd D) := by
  -- TODO
  sorry

theorem pt_rcd_has_piece (G : ctx) (s : sto) (x : Var) (T : typ) (ds : defs) (D : dec) :
  wf_sto G s → Env.binds x (val.val_new T ds) s → record_has (open_typ x T) D →
  possible_types G x (val.val_new T ds) (typ.typ_rcd D) := by
  -- TODO
  sorry

theorem pt_rcd_trm_inversion (G : ctx) (s : sto) (x : Var) (v : val) (a : trm_label) (T : typ) :
  wf_sto G s → Env.binds x v s → possible_types G x v (typ.typ_rcd (dec.dec_trm a T)) →
  ∃ S ds t, v = val.val_new S ds ∧ defs_has (open_defs x ds) (defn.def_trm a t) ∧ ty_trm ty_general sub_general G t T := by
  -- TODO
  sorry

theorem pt_rcd_typ_inversion (G : ctx) (s : sto) (x : Var) (v : val) (A : typ_label) (S U : typ) :
  wf_sto G s → Env.binds x v s → possible_types G x v (typ.typ_rcd (dec.dec_typ A S U)) →
  ∃ T ds T', v = val.val_new T ds ∧ defs_has (open_defs x ds) (defn.def_typ A T') ∧
    subtyp ty_general sub_general G S T' ∧ subtyp ty_general sub_general G T' U := by
  -- TODO
  sorry

theorem record_sub_and (T T1 T2 : typ) :
  record_type T → T = typ.typ_and T1 T2 → record_sub T T1 ∧ record_sub T T2 := by
  -- TODO
  sorry

theorem record_sub_has (T1 T2 : typ) (D : dec) :
  record_has T2 D → record_sub T1 T2 → record_has T1 D := by
  -- TODO
  sorry

theorem pt_record_sub_has (G : ctx) (x : Var) (v : val) (T1 T2 : typ) :
  (∀ D, record_has T1 D → possible_types G x v (typ.typ_rcd D)) →
  record_sub T1 T2 →
  (∀ D, record_has T2 D → possible_types G x v (typ.typ_rcd D)) := by
  -- TODO
  sorry

theorem pt_has_record (G : ctx) (x : Var) (v : val) (T : typ) :
  (∀ D, record_has T D → possible_types G x v (typ.typ_rcd D)) →
  record_type T → possible_types G x v T := by
  -- TODO
  sorry

theorem pt_has_sub (G : ctx) (x : Var) (v : val) (T U : typ) :
  (∀ D, record_has T D → possible_types G x v (typ.typ_rcd D)) →
  record_type T → record_sub T U → possible_types G x v U := by
  -- TODO
  sorry

theorem possible_types_closure_record (G : ctx) (s : sto) (x : Var) (T : typ) (ds : defs) (U : typ) :
  wf_sto G s → Env.binds x (val.val_new T ds) s → record_sub (open_typ x T) U → possible_types G x (val.val_new T ds) U := by
  -- TODO
  sorry

theorem pt_and_inversion (G : ctx) (s : sto) (x : Var) (v : val) (T1 T2 : typ) :
  wf_sto G s → Env.binds x v s → possible_types G x v (typ.typ_and T1 T2) →
  possible_types G x v T1 ∧ possible_types G x v T2 := by
  -- TODO
  sorry

-- Possible types completeness for values / tight / general

theorem possible_types_completeness_for_values (G : ctx) (s : sto) (x : Var) (v : val) (T : typ) :
  wf_sto G s → Env.binds x v s → ty_trm ty_precise sub_general G (trm.trm_val v) T → possible_types G x v T := by
  -- TODO
  sorry

theorem possible_types_completeness_tight (G : ctx) (s : sto) (x : Var) (T : typ) :
  wf_sto G s → ty_trm ty_general sub_tight G (trm.trm_var (avar.avar_f x)) T → ∃ v, Env.binds x v s ∧ possible_types G x v T := by
  -- TODO
  sorry

theorem possible_types_completeness (G : ctx) (s : sto) (x : Var) (T : typ) :
  wf_sto G s → ty_trm ty_general sub_general G (trm.trm_var (avar.avar_f x)) T → ∃ v, Env.binds x v s ∧ possible_types G x v T := by
  -- TODO
  sorry

theorem possible_types_lemma (G : ctx) (s : sto) (x : Var) (v : val) (T : typ) :
  wf_sto G s → Env.binds x v s → ty_trm ty_general sub_general G (trm.trm_var (avar.avar_f x)) T → possible_types G x v T := by
  -- TODO
  sorry

theorem ctx_binds_to_sto_binds_typing (G : ctx) (s : sto) (x : Var) (T : typ) :
  wf_sto G s → Env.binds x T G → ∃ v, Env.binds x v s ∧ ty_trm ty_precise sub_general G (trm.trm_val v) T := by
  -- TODO
  sorry

-- Basic helper lemmas

theorem var_new_typing (G : ctx) (s : sto) (x : Var) (T : typ) (ds : defs) :
  wf_sto G s → Env.binds x (val.val_new T ds) s →
  ty_trm ty_general sub_general G (trm.trm_var (avar.avar_f x)) (open_typ x T) := by
  -- TODO
  sorry

theorem new_ty_defs (G : ctx) (s : sto) (x : Var) (T : typ) (ds : defs) :
  wf_sto G s → Env.binds x (val.val_new T ds) s →
  ty_defs G (open_defs x ds) (open_typ x T) := by
  -- TODO
  sorry

theorem possible_types_closure (G : ctx) (s : sto) (x : Var) (v : val) (S T : typ) :
  wf_sto G s → Env.binds x v s → possible_types G x v S → subtyp ty_general sub_general G S T → possible_types G x v T := by
  -- TODO
  sorry

-- Canonical forms and safety

theorem canonical_forms_1 (G : ctx) (s : sto) (x : Var) (T U : typ) :
  wf_sto G s → ty_trm ty_general sub_general G (trm.trm_var (avar.avar_f x)) (typ.typ_all T U) →
  ∃ (L : Vars) (T' : typ) (t : trm), Env.binds x (val.val_lambda T' t) s ∧ subtyp ty_general sub_general G T T' ∧
            (∀ y, y ∉ L → ty_trm ty_general sub_general ((y, T) :: G) (open_trm y t) (open_typ y U)) := by
  -- TODO
  sorry

theorem canonical_forms_2 (G : ctx) (s : sto) (x : Var) (a : trm_label) (T : typ) :
  wf_sto G s → ty_trm ty_general sub_general G (trm.trm_var (avar.avar_f x)) (typ.typ_rcd (dec.dec_trm a T)) →
  ∃ S ds t, Env.binds x (val.val_new S ds) s ∧ ty_defs G (open_defs x ds) (open_typ x S) ∧ defs_has (open_defs x ds) (defn.def_trm a t) ∧
             ty_trm ty_general sub_general G t T := by
  -- TODO
  sorry

theorem var_typing_implies_avar_f (G : ctx) (a : avar) (T : typ) :
  ty_trm ty_general sub_general G (trm.trm_var a) T → ∃ x, a = avar.avar_f x := by
  -- TODO
  sorry

theorem val_typing (G : ctx) (v : val) (T : typ) :
  ty_trm ty_general sub_general G (trm.trm_val v) T →
  ∃ T', ty_trm ty_precise sub_general G (trm.trm_val v) T' ∧ subtyp ty_general sub_general G T' T := by
  -- TODO
  sorry

theorem safety (G : ctx) (s : sto) (t : trm) (T : typ) :
  wf_sto G s → ty_trm ty_general sub_general G t T →
  (normal_form t ∨ (∃ s' t' G' G'', red t s t' s' ∧ G' = G ++ G'' ∧ ty_trm ty_general sub_general G' t' T ∧ wf_sto G' s')) := by
  -- TODO
  sorry

end Lp2lc.Active.Dot_top_bot
