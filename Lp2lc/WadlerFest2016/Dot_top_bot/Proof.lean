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
    change x ∈ ((List.map (λ p : Var × A => p.fst) (E ++ [(x, a)])).toFinset)
    simp [List.map_append]
  exact hx hx_mem

-- ######################################################################
-- Weakening (statements only; proofs deferred)

theorem weaken_rules :
  (∀ m1 m2 G t T, TyTrm m1 m2 G t T → ∀ G1 G2 G3,
     G = G1 ++ G3 →
     Lp2lc.Active.ok (G1 ++ G2 ++ G3) →
     TyTrm m1 m2 (G1 ++ G2 ++ G3) t T) ∧
  (∀ G d D, TyDef G d D → ∀ G1 G2 G3,
     G = G1 ++ G3 →
     Lp2lc.Active.ok (G1 ++ G2 ++ G3) →
     TyDef (G1 ++ G2 ++ G3) d D) ∧
  (∀ G ds T, TyDefs G ds T → ∀ G1 G2 G3,
     G = G1 ++ G3 →
     Lp2lc.Active.ok (G1 ++ G2 ++ G3) →
     TyDefs (G1 ++ G2 ++ G3) ds T) ∧
  (∀ m1 m2 G T U, Subtyp m1 m2 G T U → ∀ G1 G2 G3,
     G = G1 ++ G3 →
     Lp2lc.Active.ok (G1 ++ G2 ++ G3) →
     Subtyp m1 m2 (G1 ++ G2 ++ G3) T U) := by
  -- TODO: mutual induction on Typing/subtyping rules
  sorry

/-- Weakening for term Typing. -/
theorem weaken_ty_trm (m1 m2) (G1 G2 : Ctx) (t : Trm) (T : Typ) :
  TyTrm m1 m2 G1 t T →
  Lp2lc.Active.ok (G1 ++ G2) →
  TyTrm m1 m2 (G1 ++ G2) t T := by
  -- TODO: derive from weaken_rules
  sorry

/-- Weakening for subtyping. -/
theorem weaken_subtyp (m1 m2) (G1 G2 : Ctx) (S U : Typ) :
  Subtyp m1 m2 G1 S U →
  Lp2lc.Active.ok (G1 ++ G2) →
  Subtyp m1 m2 (G1 ++ G2) S U := by
  -- TODO: derive from weaken_rules
  sorry

-- ######################################################################
-- Well-formed store (statements)

theorem wf_sto_to_ok_s (s : Sto) (G : Ctx) :
  WfSto G s → Lp2lc.Active.ok s := by
  -- TODO: structural induction on WfSto
  sorry


theorem wf_sto_to_ok_G (s : Sto) (G : Ctx) :
  WfSto G s → Lp2lc.Active.ok G := by
  -- TODO: structural induction on WfSto
  sorry

-- ######################################################################
-- Store/context relation helpers (statements)

theorem ctx_binds_to_sto_binds_raw (s : Sto) (G : Ctx) (x : Var) (T : Typ) :
  WfSto G s →
  Env.binds x T G →
  ∃ G1 G2 v, G = G1 ++ ((x, T) :: G2) ∧ Env.binds x v s ∧ TyTrm ty_precise sub_general G1 (Trm.trm_val v) T := by
  -- TODO
  sorry


theorem sto_binds_to_ctx_binds_raw (s : Sto) (G : Ctx) (x : Var) (v : Val) :
  WfSto G s →
  Env.binds x v s →
  ∃ G1 G2 T, G = G1 ++ ((x, T) :: G2) ∧ TyTrm ty_precise sub_general G1 (Trm.trm_val v) T := by
  -- TODO
  sorry


theorem invert_wf_sto_concat (s : Sto) (G1 G2 : Ctx) :
  WfSto (G1 ++ G2) s → ∃ s1 s2, s = s1 ++ s2 ∧ WfSto G1 s1 := by
  -- TODO
  sorry


theorem sto_unbound_to_ctx_unbound (s : Sto) (G : Ctx) (x : Var) :
  WfSto G s → x ∉ Env.dom s → x ∉ Env.dom G := by
  -- TODO
  sorry


theorem ctx_unbound_to_sto_unbound (s : Sto) (G : Ctx) (x : Var) :
  WfSto G s → x ∉ Env.dom G → x ∉ Env.dom s := by
  -- TODO
  sorry

-- ######################################################################
-- Typing inversions (statements)

theorem typing_implies_bound (m1 m2) (G : Ctx) (x : Var) (T : Typ) :
  TyTrm m1 m2 G (Trm.trm_var (Avar.avar_f x)) T → ∃ S, Env.binds x S G := by
  -- TODO: inversion on Typing
  sorry


theorem typing_bvar_implies_false (m1 m2) (G : Ctx) (a : Nat) (T : Typ) :
  TyTrm m1 m2 G (Trm.trm_var (Avar.avar_b a)) T → False := by
  -- TODO: inversion on Typing
  sorry

-- ######################################################################
-- Extra Rec (statements)

theorem extra_bnd_rules :
  (∀ m1 m2 G t T, TyTrm m1 m2 G t T → ∀ G1 G2 x S G',
    G = G1 ++ ((x, open_typ x S) :: G2) →
    G' = G1 ++ ((x, Typ.typ_bnd S) :: G2) →
    TyTrm m1 m2 G' t T)
  ∧ (∀ G d D, TyDef G d D → ∀ G1 G2 x S G',
    G = G1 ++ ((x, open_typ x S) :: G2) →
    G' = G1 ++ ((x, Typ.typ_bnd S) :: G2) →
    TyDef G' d D)
  ∧ (∀ G ds T, TyDefs G ds T → ∀ G1 G2 x S G',
    G = G1 ++ ((x, open_typ x S) :: G2) →
    G' = G1 ++ ((x, Typ.typ_bnd S) :: G2) →
    TyDefs G' ds T)
  ∧ (∀ m1 m2 G T U, Subtyp m1 m2 G T U → ∀ G1 G2 x S G',
    G = G1 ++ ((x, open_typ x S) :: G2) →
    G' = G1 ++ ((x, Typ.typ_bnd S) :: G2) →
    Subtyp m1 m2 G' T U) := by
  -- TODO: mutual induction on Typing/subtyping rules
  sorry

-- ######################################################################
-- Substitution — freshness and commuting (statements)

theorem subst_fresh_avar : ∀ (x y : Var), ∀ a : Avar,
  x ∉ fv_avar a → subst_avar x y a = a := by
  -- TODO: by cases on a
  sorry

theorem subst_fresh_typ_dec : ∀ (x y : Var),
  (∀ T : Typ, x ∉ fv_typ T → subst_typ x y T = T) ∧
  (∀ D : Dec, x ∉ fv_dec D → subst_dec x y D = D) := by
  -- TODO: mutual structural induction
  sorry

theorem subst_fresh_trm_val_def_defs : ∀ (x y : Var),
  (∀ t : Trm, x ∉ fv_trm t → subst_trm x y t = t) ∧
  (∀ v : Val, x ∉ fv_val v → subst_val x y v = v) ∧
  (∀ d : Defn, x ∉ fv_def d → subst_def x y d = d) ∧
  (∀ ds : Defs, x ∉ fv_defs ds → subst_defs x y ds = ds) := by
  -- TODO: mutual structural induction
  sorry

theorem invert_fv_ctx_types_push : ∀ (x z : Var) (T : Typ) (G : Ctx),
  x ∉ fv_ctx_types ((z, T) :: G) → x ∉ fv_typ T ∧ x ∉ fv_ctx_types G := by
  -- TODO
  sorry

theorem subst_fresh_ctx : ∀ (x y : Var) (G : Ctx),
  x ∉ fv_ctx_types G → subst_ctx x y G = G := by
  -- TODO: Env fold + projections
  sorry

theorem subst_open_commute_avar : ∀ (x y u : Var), ∀ a : Avar, ∀ n : Nat,
  subst_avar x y (open_rec_avar n u a) =
  open_rec_avar n (subst_fvar x y u) (subst_avar x y a) := by
  -- TODO
  sorry

theorem subst_open_commute_typ_dec : ∀ (x y u : Var),
  (∀ t : Typ, ∀ n : Nat,
     subst_typ x y (open_rec_typ n u t) =
     open_rec_typ n (subst_fvar x y u) (subst_typ x y t)) ∧
  (∀ D : Dec, ∀ n : Nat,
     subst_dec x y (open_rec_dec n u D) =
     open_rec_dec n (subst_fvar x y u) (subst_dec x y D)) := by
  -- TODO: mutual structural induction
  sorry

theorem subst_open_commute_typ : ∀ (x y u : Var) (T : Typ),
  subst_typ x y (open_typ u T) = open_typ (subst_fvar x y u) (subst_typ x y T) := by
  -- TODO: from subst_open_commute_typ_dec
  sorry

theorem subst_open_commute_dec : ∀ (x y u : Var) (D : Dec),
  subst_dec x y (open_dec u D) = open_dec (subst_fvar x y u) (subst_dec x y D) := by
  -- TODO: from subst_open_commute_typ_dec
  sorry

theorem subst_open_commute_trm_val_def_defs : ∀ (x y u : Var),
  (∀ t : Trm, ∀ n : Nat,
     subst_trm x y (open_rec_trm n u t) =
     open_rec_trm n (subst_fvar x y u) (subst_trm x y t)) ∧
  (∀ v : Val, ∀ n : Nat,
     subst_val x y (open_rec_val n u v) =
     open_rec_val n (subst_fvar x y u) (subst_val x y v)) ∧
  (∀ d : Defn, ∀ n : Nat,
     subst_def x y (open_rec_def n u d) =
     open_rec_def n (subst_fvar x y u) (subst_def x y d)) ∧
  (∀ ds : Defs, ∀ n : Nat,
     subst_defs x y (open_rec_defs n u ds) =
     open_rec_defs n (subst_fvar x y u) (subst_defs x y ds)) := by
  -- TODO: mutual structural induction
  sorry

theorem subst_open_commute_trm : ∀ (x y u : Var) (t : Trm),
  subst_trm x y (open_trm u t) = open_trm (subst_fvar x y u) (subst_trm x y t) := by
  -- TODO: from subst_open_commute_trm_val_def_defs
  sorry

theorem subst_open_commute_val : ∀ (x y u : Var) (v : Val),
  subst_val x y (open_val u v) = open_val (subst_fvar x y u) (subst_val x y v) := by
  -- TODO: from subst_open_commute_trm_val_def_defs
  sorry

theorem subst_open_commute_defs : ∀ (x y u : Var) (ds : Defs),
  subst_defs x y (open_defs u ds) = open_defs (subst_fvar x y u) (subst_defs x y ds) := by
  -- TODO: from subst_open_commute_trm_val_def_defs
  sorry

-- Substitution — intro and undo (statements)

theorem subst_intro_trm : ∀ (x u : Var) (t : Trm),
  x ∉ fv_trm t → open_trm u t = subst_trm x u (open_trm x t) := by
  -- TODO
  sorry

theorem subst_intro_val : ∀ (x u : Var) (v : Val),
  x ∉ fv_val v → open_val u v = subst_val x u (open_val x v) := by
  -- TODO
  sorry

theorem subst_intro_defs : ∀ (x u : Var) (ds : Defs),
  x ∉ fv_defs ds → open_defs u ds = subst_defs x u (open_defs x ds) := by
  -- TODO
  sorry

theorem subst_intro_typ : ∀ (x u : Var) (T : Typ),
  x ∉ fv_typ T → open_typ u T = subst_typ x u (open_typ x T) := by
  -- TODO
  sorry

theorem subst_intro_dec : ∀ (x u : Var) (D : Dec),
  x ∉ fv_dec D → open_dec u D = subst_dec x u (open_dec x D) := by
  -- TODO
  sorry

theorem subst_undo_avar : ∀ (x y : Var),
  (∀ a : Avar, y ∉ fv_avar a → subst_avar y x (subst_avar x y a) = a) := by
  -- TODO
  sorry

theorem subst_undo_typ_dec : ∀ (x y : Var),
  (∀ T : Typ, y ∉ fv_typ T → subst_typ y x (subst_typ x y T) = T) ∧
  (∀ D : Dec, y ∉ fv_dec D → subst_dec y x (subst_dec x y D) = D) := by
  -- TODO
  sorry

theorem subst_undo_trm_val_def_defs : ∀ (x y : Var),
  (∀ t : Trm, y ∉ fv_trm t → subst_trm y x (subst_trm x y t) = t) ∧
  (∀ v : Val, y ∉ fv_val v → subst_val y x (subst_val x y v) = v) ∧
  (∀ d : Defn, y ∉ fv_def d → subst_def y x (subst_def x y d) = d) ∧
  (∀ ds : Defs, y ∉ fv_defs ds → subst_defs y x (subst_defs x y ds) = ds) := by
  -- TODO
  sorry

-- Further substitution lemmas (undo/idempotence) and Label invariants

theorem subst_typ_undo (x y : Var) (T : Typ) :
  y ∉ fv_typ T → subst_typ y x (subst_typ x y T) = T := by
  -- TODO
  sorry

theorem subst_trm_undo (x y : Var) (t : Trm) :
  y ∉ fv_trm t → subst_trm y x (subst_trm x y t) = t := by
  -- TODO
  sorry

theorem subst_idempotent_avar (x y : Var) :
  (∀ a : Avar, subst_avar x y (subst_avar x y a) = subst_avar x y a) := by
  -- TODO
  sorry

theorem subst_idempotent_typ_dec (x y : Var) :
  (∀ T : Typ, subst_typ x y (subst_typ x y T) = subst_typ x y T) ∧
  (∀ D : Dec, subst_dec x y (subst_dec x y D) = subst_dec x y D) := by
  -- TODO
  sorry

theorem subst_idempotent_trm_val_def_defs (x y : Var) :
  (∀ t : Trm, subst_trm x y (subst_trm x y t) = subst_trm x y t) ∧
  (∀ v : Val, subst_val x y (subst_val x y v) = subst_val x y v) ∧
  (∀ d : Defn, subst_def x y (subst_def x y d) = subst_def x y d) ∧
  (∀ ds : Defs, subst_defs x y (subst_defs x y ds) = subst_defs x y ds) := by
  -- TODO
  sorry

theorem subst_typ_idempotent (x y : Var) (T : Typ) :
  subst_typ x y (subst_typ x y T) = subst_typ x y T := by
  -- TODO
  sorry

theorem subst_trm_idempotent (x y : Var) (t : Trm) :
  subst_trm x y (subst_trm x y t) = subst_trm x y t := by
  -- TODO
  sorry

theorem subst_label_of_dec (x y : Var) (D : Dec) :
  label_of_dec D = label_of_dec (subst_dec x y D) := by
  -- TODO
  sorry

theorem subst_label_of_def (x y : Var) (d : Defn) :
  label_of_def d = label_of_def (subst_def x y d) := by
  -- TODO
  sorry

theorem subst_defs_hasnt (x y : Var) (l : Label) (ds : Defs) :
  defs_hasnt ds l → defs_hasnt (subst_defs x y ds) l := by
  -- TODO
  sorry

-- ######################################################################
-- Substitution principle (statements)

theorem subst_rules (y : Var) (S : Typ) :
  (∀ m1 m2 G t T, TyTrm m1 m2 G t T → ∀ G1 G2 x,
     G = G1 ++ ((x, S) :: G2) →
     Lp2lc.Active.ok (G1 ++ ((x, S) :: G2)) →
     y ∉ fv_ctx_types G1 →
     TyTrm ty_general sub_general (G1 ++ subst_ctx x y G2) (Trm.trm_var (Avar.avar_f y)) (subst_typ x y S) →
     m1 = ty_general → m2 = sub_general →
     TyTrm m1 m2 (G1 ++ subst_ctx x y G2) (subst_trm x y t) (subst_typ x y T)) ∧
  (∀ G d D, TyDef G d D → ∀ G1 G2 x,
     G = G1 ++ ((x, S) :: G2) →
     Lp2lc.Active.ok (G1 ++ ((x, S) :: G2)) →
     y ∉ fv_ctx_types G1 →
     TyTrm ty_general sub_general (G1 ++ subst_ctx x y G2) (Trm.trm_var (Avar.avar_f y)) (subst_typ x y S) →
     TyDef (G1 ++ subst_ctx x y G2) (subst_def x y d) (subst_dec x y D)) ∧
  (∀ G ds T, TyDefs G ds T → ∀ G1 G2 x,
     G = G1 ++ ((x, S) :: G2) →
     Lp2lc.Active.ok (G1 ++ ((x, S) :: G2)) →
     y ∉ fv_ctx_types G1 →
     TyTrm ty_general sub_general (G1 ++ subst_ctx x y G2) (Trm.trm_var (Avar.avar_f y)) (subst_typ x y S) →
     TyDefs (G1 ++ subst_ctx x y G2) (subst_defs x y ds) (subst_typ x y T)) ∧
  (∀ m1 m2 G T U, Subtyp m1 m2 G T U → ∀ G1 G2 x,
     G = G1 ++ ((x, S) :: G2) →
     Lp2lc.Active.ok (G1 ++ ((x, S) :: G2)) →
     y ∉ fv_ctx_types G1 →
     TyTrm ty_general sub_general (G1 ++ subst_ctx x y G2) (Trm.trm_var (Avar.avar_f y)) (subst_typ x y S) →
     m1 = ty_general → m2 = sub_general →
     Subtyp m1 m2 (G1 ++ subst_ctx x y G2) (subst_typ x y T) (subst_typ x y U)) := by
  -- TODO
  sorry

theorem subst_ty_trm (y : Var) (S : Typ) (G : Ctx) (x : Var) (t : Trm) (T : Typ) :
  TyTrm ty_general sub_general (G ++ [(x, S)]) t T →
  Lp2lc.Active.ok (G ++ [(x, S)]) →
  y ∉ fv_ctx_types G →
  TyTrm ty_general sub_general G (Trm.trm_var (Avar.avar_f y)) (subst_typ x y S) →
  TyTrm ty_general sub_general G (subst_trm x y t) (subst_typ x y T) := by
  -- TODO
  sorry

theorem subst_ty_defs (y : Var) (S : Typ) (G : Ctx) (x : Var) (ds : Defs) (T : Typ) :
  TyDefs (G ++ [(x, S)]) ds T →
  Lp2lc.Active.ok (G ++ [(x, S)]) →
  y ∉ fv_ctx_types G →
  TyTrm ty_general sub_general G (Trm.trm_var (Avar.avar_f y)) (subst_typ x y S) →
  TyDefs G (subst_defs x y ds) (subst_typ x y T) := by
  -- TODO
  sorry

-- ######################################################################
-- Some lemmas (statements)

theorem corresponding_types (G : Ctx) (s : Sto) (x : Var) (T : Typ) :
  WfSto G s → Env.binds x T G →
  ((∃ S U t, Env.binds x (Val.val_lambda S t) s ∧
             TyTrm ty_precise sub_general G (Trm.trm_val (Val.val_lambda S t)) (Typ.typ_all S U) ∧
             T = Typ.typ_all S U)
   ∨ (∃ S ds, Env.binds x (Val.val_new S ds) s ∧
              TyTrm ty_precise sub_general G (Trm.trm_val (Val.val_new S ds)) (Typ.typ_bnd S) ∧
              T = Typ.typ_bnd S)) := by
  -- TODO
  sorry

theorem unique_rec_subtyping (G : Ctx) (S T : Typ) :
  Subtyp ty_precise sub_general G (Typ.typ_bnd S) T → T = Typ.typ_bnd S := by
  -- TODO
  sorry

theorem unique_all_subtyping (G : Ctx) (S U T : Typ) :
  Subtyp ty_precise sub_general G (Typ.typ_all S U) T → T = Typ.typ_all S U := by
  -- TODO
  sorry

theorem unique_lambda_typing (G : Ctx) (x : Var) (S U T : Typ) :
  Env.binds x (Typ.typ_all S U) G →
  TyTrm ty_precise sub_general G (Trm.trm_var (Avar.avar_f x)) T →
  T = Typ.typ_all S U := by
  -- TODO
  sorry

theorem lambda_not_rcd (G : Ctx) (x : Var) (S U : Typ) (A : TypLabel) (T : Typ) :
  Env.binds x (Typ.typ_all S U) G →
  TyTrm ty_precise sub_general G (Trm.trm_var (Avar.avar_f x)) (Typ.typ_rcd (Dec.dec_typ A T T)) → False := by
  -- TODO
  sorry

-- Record opening/Label preservation

theorem open_dec_preserves_label (D : Dec) (x : Var) (i : Nat) :
  label_of_dec D = label_of_dec (open_rec_dec i x D) := by
  -- TODO
  sorry

theorem open_record_dec (D : Dec) (x : Var) :
  RecordDec D → RecordDec (open_dec x D) := by
  -- TODO
  sorry

theorem open_record_typ (T : Typ) (x : Var) (ls : Finset Label) :
  RecordTyp T ls → RecordTyp (open_typ x T) ls := by
  -- TODO
  sorry

theorem open_eq_avar (x : Var) (i : Nat) (a1 a2 : Avar) :
  x ∉ fv_avar a1 → x ∉ fv_avar a2 →
  open_rec_avar i x a1 = open_rec_avar i x a2 → a1 = a2 := by
  -- TODO
  sorry

theorem open_eq_typ_dec (x : Var) :
  (∀ T1 : Typ, x ∉ fv_typ T1 → ∀ T2 : Typ, x ∉ fv_typ T2 → ∀ i : Nat,
     open_rec_typ i x T1 = open_rec_typ i x T2 → T1 = T2) ∧
  (∀ D1 : Dec, x ∉ fv_dec D1 → ∀ D2 : Dec, x ∉ fv_dec D2 → ∀ i : Nat,
     open_rec_dec i x D1 = open_rec_dec i x D2 → D1 = D2) := by
  -- TODO
  sorry

theorem open_eq_typ (x : Var) (i : Nat) (T1 T2 : Typ) :
  x ∉ fv_typ T1 → x ∉ fv_typ T2 →
  open_rec_typ i x T1 = open_rec_typ i x T2 → T1 = T2 := by
  -- TODO
  sorry

theorem open_record_dec_rev (D : Dec) (x : Var) :
  x ∉ fv_dec D → RecordDec (open_dec x D) → RecordDec D := by
  -- TODO
  sorry

theorem open_record_typ_rev (T : Typ) (x : Var) (ls : Finset Label) :
  x ∉ fv_typ T → RecordTyp (open_typ x T) ls → RecordTyp T ls := by
  -- TODO
  sorry

theorem open_record_type (T : Typ) (x : Var) :
  record_type T → record_type (open_typ x T) := by
  -- TODO
  sorry

theorem open_record_type_rev (T : Typ) (x : Var) :
  x ∉ fv_typ T → record_type (open_typ x T) → record_type T := by
  -- TODO
  sorry

theorem label_same_typing (G : Ctx) (d : Defn) (D : Dec) :
  TyDef G d D → label_of_def d = label_of_dec D := by
  -- TODO
  sorry

theorem record_defs_typing_rec (G : Ctx) (ds : Defs) (S : Typ) :
  TyDefs G ds S → ∃ ls, RecordTyp S ls ∧ ∀ l, l ∉ ls ↔ defs_hasnt ds l := by
  -- TODO
  sorry

theorem record_defs_typing (G : Ctx) (ds : Defs) (S : Typ) :
  TyDefs G ds S → record_type S := by
  -- TODO
  sorry

theorem record_new_typing (G : Ctx) (S : Typ) (ds : Defs) :
  TyTrm ty_precise sub_general G (Trm.trm_val (Val.val_new S ds)) (Typ.typ_bnd S) →
  record_type S := by
  -- TODO
  sorry

-- ######################################################################
-- Narrowing (statements)

def subenv_def := subenv -- local alias to emphasize usage

theorem subenv_push (G G' : Ctx) (x : Var) (T : Typ) :
  subenv_def G' G → Lp2lc.Active.ok ((x, T) :: G') → subenv_def ((x, T) :: G') ((x, T) :: G) := by
  -- TODO
  sorry

theorem subenv_last (G : Ctx) (x : Var) (S U : Typ) :
  Subtyp ty_general sub_general G S U → Lp2lc.Active.ok (G ++ [(x, S)]) → subenv_def (G ++ [(x, S)]) (G ++ [(x, U)]) := by
  -- TODO
  sorry

theorem narrow_rules :
  (∀ m1 m2 G t T, TyTrm m1 m2 G t T → ∀ G',
     m1 = ty_general → m2 = sub_general → Lp2lc.Active.ok G' → subenv_def G' G → TyTrm m1 m2 G' t T) ∧
  (∀ G d D, TyDef G d D → ∀ G', Lp2lc.Active.ok G' → subenv_def G' G → TyDef G' d D) ∧
  (∀ G ds T, TyDefs G ds T → ∀ G', Lp2lc.Active.ok G' → subenv_def G' G → TyDefs G' ds T) ∧
  (∀ m1 m2 G S U, Subtyp m1 m2 G S U → ∀ G',
     m1 = ty_general → m2 = sub_general → Lp2lc.Active.ok G' → subenv_def G' G → Subtyp m1 m2 G' S U) := by
  -- TODO
  sorry

theorem narrow_typing (G G' : Ctx) (t : Trm) (T : Typ) :
  TyTrm ty_general sub_general G t T → subenv_def G' G → Lp2lc.Active.ok G' → TyTrm ty_general sub_general G' t T := by
  -- TODO
  sorry

theorem narrow_subtyping (G G' : Ctx) (S U : Typ) :
  Subtyp ty_general sub_general G S U → subenv_def G' G → Lp2lc.Active.ok G' → Subtyp ty_general sub_general G' S U := by
  -- TODO
  sorry

-- ######################################################################
-- Has-member inversions and helpers (statements)

theorem has_member_rules_inv (G : Ctx) (x : Var) (T : Typ) (A : TypLabel) (S U : Typ) :
  HasMemberRules G x T A S U →
  (T = Typ.typ_rcd (Dec.dec_typ A S U)) ∨
  (∃ T1 T2, T = Typ.typ_and T1 T2 ∧ (HasMember G x T1 A S U ∨ HasMember G x T2 A S U)) ∨
  (∃ T', T = Typ.typ_bnd T' ∧ HasMember G x (open_typ x T') A S U) ∨
  (∃ y B T' m1 m2, T = Typ.typ_sel (Avar.avar_f y) B ∧
     TyTrm m1 m2 G (Trm.trm_var (Avar.avar_f y)) (Typ.typ_rcd (Dec.dec_typ B T' T')) ∧
     HasMember G x T' A S U) ∨
  (T = Typ.typ_bot) := by
  intro proofOfBottom
  cases proofOfBottom with
  | has_refl _ _ _ _ _ =>
      exact Or.inl rfl
  | has_and1 _ _ T1 T2 _ _ _ proofOfBottom =>
      exact Or.inr (Or.inl ⟨T1, T2, rfl, Or.inl proofOfBottom⟩)
  | has_and2 _ _ T1 T2 _ _ _ proofOfBottom =>
      exact Or.inr (Or.inl ⟨T1, T2, rfl, Or.inr proofOfBottom⟩)
  | has_bnd _ _ T' _ _ _ proofOfBottom =>
      exact Or.inr (Or.inr (Or.inl ⟨T', rfl, proofOfBottom⟩))
  | has_sel _ _ y B T' _ _ _ proofOfTyping proofOfBottom =>
      refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      exact ⟨y, B, T', _, _, rfl, proofOfTyping, proofOfBottom⟩
  | has_bot _ _ _ _ _ =>
      exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem has_member_inv (G : Ctx) (x : Var) (T : Typ) (A : TypLabel) (S U : Typ) :
  HasMember G x T A S U →
  (T = Typ.typ_rcd (Dec.dec_typ A S U)) ∨
  (∃ T1 T2, T = Typ.typ_and T1 T2 ∧ (HasMember G x T1 A S U ∨ HasMember G x T2 A S U)) ∨
  (∃ T', T = Typ.typ_bnd T' ∧ HasMember G x (open_typ x T') A S U) ∨
  (∃ y B T' m1 m2, T = Typ.typ_sel (Avar.avar_f y) B ∧
     TyTrm m1 m2 G (Trm.trm_var (Avar.avar_f y)) (Typ.typ_rcd (Dec.dec_typ B T' T')) ∧
     HasMember G x T' A S U) ∨
  (T = Typ.typ_bot) := by
  intro proofOfBottom
  cases proofOfBottom with
  | has_any G x T A S U _ proofOfBottom =>
      exact has_member_rules_inv G x T A S U proofOfBottom

theorem has_member_covariance (G : Ctx) (s : Sto) (T1 T2 : Typ) (x : Var)
    (A : TypLabel) (S2 U2 : Typ) :
  WfSto G s →
  Subtyp ty_general sub_tight G T1 T2 →
  TyTrm ty_general sub_tight G (Trm.trm_var (Avar.avar_f x)) T1 →
  HasMember G x T2 A S2 U2 →
  ∃ S1 U1, HasMember G x T1 A S1 U1 ∧
           Subtyp ty_general sub_tight G S2 S1 ∧
           Subtyp ty_general sub_tight G U1 U2 := by
  -- TODO
  sorry

theorem has_member_monotonicity (G : Ctx) (s : Sto) (x : Var) (T0 : Typ) (ds : Defs)
    (T : Typ) (A : TypLabel) (S U : Typ) :
  WfSto G s →
  Env.binds x (Val.val_new T0 ds) s →
  HasMember G x T A S U →
  ∃ T1, HasMember G x (Typ.typ_bnd T0) A T1 T1 ∧
        Subtyp ty_general sub_tight G S T1 ∧
        Subtyp ty_general sub_tight G T1 U := by
  -- TODO
  sorry

-- ######################################################################
-- Mode conversions and store-context relations (derived)

theorem precise_to_general :
  (∀ m1 m2 G t T, TyTrm m1 m2 G t T → m1 = ty_precise → m2 = sub_general → TyTrm ty_general sub_general G t T) ∧
  (∀ m1 m2 G S U, Subtyp m1 m2 G S U → m1 = ty_precise → m2 = sub_general → Subtyp ty_general sub_general G S U) := by
  -- TODO
  sorry

theorem precise_to_general_typing (G : Ctx) (t : Trm) (T : Typ) :
  TyTrm ty_precise sub_general G t T → TyTrm ty_general sub_general G t T := by
  -- TODO
  sorry

theorem tight_to_general :
  (∀ m1 m2 G t T, TyTrm m1 m2 G t T → m1 = ty_general → m2 = sub_tight → TyTrm ty_general sub_general G t T) ∧
  (∀ m1 m2 G S U, Subtyp m1 m2 G S U → m1 = ty_general → m2 = sub_tight → Subtyp ty_general sub_general G S U) := by
  -- TODO
  sorry

theorem tight_to_general_typing (G : Ctx) (t : Trm) (T : Typ) :
  TyTrm ty_general sub_tight G t T → TyTrm ty_general sub_general G t T := by
  -- TODO
  sorry

theorem tight_to_general_subtyping (G : Ctx) (S U : Typ) :
  Subtyp ty_general sub_tight G S U → Subtyp ty_general sub_general G S U := by
  -- TODO
  sorry

theorem precise_to_tight :
  (∀ m1 m2 G t T, TyTrm m1 m2 G t T → m1 = ty_precise → m2 = sub_general → TyTrm ty_general sub_tight G t T) ∧
  (∀ m1 m2 G S U, Subtyp m1 m2 G S U → m1 = ty_precise → m2 = sub_general → Subtyp ty_general sub_tight G S U) := by
  -- TODO
  sorry

theorem precise_to_tight_typing (G : Ctx) (t : Trm) (T : Typ) :
  TyTrm ty_precise sub_general G t T → TyTrm ty_general sub_tight G t T := by
  -- TODO
  sorry

theorem general_to_tight (G0 : Ctx) (s0 : Sto) :
  WfSto G0 s0 →
  (∀ m1 m2 G t T, TyTrm m1 m2 G t T → G = G0 → m1 = ty_general → m2 = sub_general → TyTrm ty_general sub_tight G t T) ∧
  (∀ m1 m2 G S U, Subtyp m1 m2 G S U → G = G0 → m1 = ty_general → m2 = sub_general → Subtyp ty_general sub_tight G S U) := by
  -- TODO
  sorry

theorem general_to_tight_subtyping (G : Ctx) (s : Sto) (S U : Typ) :
  WfSto G s → Subtyp ty_general sub_general G S U → Subtyp ty_general sub_tight G S U := by
  -- TODO
  sorry

theorem sto_binds_to_ctx_binds (G : Ctx) (s : Sto) (x : Var) (v : Val) :
  WfSto G s → Env.binds x v s → ∃ S, Env.binds x S G := by
  -- TODO
  sorry

theorem ctx_binds_to_sto_binds (G : Ctx) (s : Sto) (x : Var) (T : Typ) :
  WfSto G s → Env.binds x T G → ∃ v, Env.binds x v s := by
  -- TODO
  sorry

theorem val_new_typing (G : Ctx) (s : Sto) (x : Var) (T : Typ) (ds : Defs) :
  WfSto G s → Env.binds x (Val.val_new T ds) s →
  TyTrm ty_precise sub_general G (Trm.trm_val (Val.val_new T ds)) (Typ.typ_bnd T) := by
  -- TODO
  sorry

-- ######################################################################
-- Record-Sub lemmas (statements)

theorem record_typ_sub_closed (T T' : Typ) (ls : Finset Label) :
  RecordSub T T' → RecordTyp T ls → ∃ ls', RecordTyp T' ls' ∧ ls' ⊆ ls := by
  -- TODO
  sorry

theorem record_type_sub_closed (T T' : Typ) :
  RecordSub T T' → record_type T → record_type T' := by
  -- TODO
  sorry

theorem record_sub_trans (T1 T2 T3 : Typ) :
  RecordSub T1 T2 → RecordSub T2 T3 → RecordSub T1 T3 := by
  -- TODO
  sorry

theorem record_subtyping (G : Ctx) (T T' : Typ) :
  Subtyp ty_precise sub_general G T T' → record_type T → RecordSub T T' := by
  -- TODO
  sorry

theorem record_typ_sub_label_in (T : Typ) (D : Dec) (ls : Finset Label) :
  RecordTyp T ls → RecordSub T (Typ.typ_rcd D) → label_of_dec D ∈ ls := by
  -- TODO
  sorry

theorem rcd_typ_eq_bounds (T : Typ) (A : TypLabel) (S U : Typ) :
  record_type T → RecordSub T (Typ.typ_rcd (Dec.dec_typ A S U)) → S = U := by
  -- TODO
  sorry

theorem unique_rcd_typ (T : Typ) (A : TypLabel) (T1 T2 : Typ) :
  record_type T →
  RecordSub T (Typ.typ_rcd (Dec.dec_typ A T1 T1)) →
  RecordSub T (Typ.typ_rcd (Dec.dec_typ A T2 T2)) →
  T1 = T2 := by
  -- TODO
  sorry

theorem record_type_sub_not_rec (S T : Typ) (x : Var) :
  RecordSub (open_typ x S) (Typ.typ_bnd T) → record_type S → False := by
  -- TODO
  sorry

theorem shape_new_typing (G : Ctx) (x : Var) (S T : Typ) :
  Env.binds x (Typ.typ_bnd S) G → record_type S →
  TyTrm ty_precise sub_general G (Trm.trm_var (Avar.avar_f x)) T →
  T = Typ.typ_bnd S ∨ RecordSub (open_typ x S) T := by
  -- TODO
  sorry

theorem unique_tight_bounds (G : Ctx) (s : Sto) (x : Var) (T1 T2 : Typ) (A : TypLabel) :
  WfSto G s →
  TyTrm ty_precise sub_general G (Trm.trm_var (Avar.avar_f x)) (Typ.typ_rcd (Dec.dec_typ A T1 T1)) →
  TyTrm ty_precise sub_general G (Trm.trm_var (Avar.avar_f x)) (Typ.typ_rcd (Dec.dec_typ A T2 T2)) →
  T1 = T2 := by
  -- TODO
  sorry

-- ######################################################################
-- More record/Has-member lemmas and possible types (statements)

theorem record_type_new (G : Ctx) (s : Sto) (x : Var) (T : Typ) (ds : Defs) :
  WfSto G s → Env.binds x (Val.val_new T ds) s → record_type (open_typ x T) := by
  -- TODO
  sorry

theorem has_member_rcd_typ_sub2_mut :
  ((∀ G x T A S U, HasMember G x T A S U → record_type T →
      (T = (Typ.typ_rcd (Dec.dec_typ A S U)) ∨ Subtyp ty_precise sub_general G T (Typ.typ_rcd (Dec.dec_typ A S U)))) ∧
   (∀ G x T A S U, HasMemberRules G x T A S U → record_type T →
      (T = (Typ.typ_rcd (Dec.dec_typ A S U)) ∨ Subtyp ty_precise sub_general G T (Typ.typ_rcd (Dec.dec_typ A S U))))) := by
  -- TODO
  sorry

theorem wf_sto_val_new_in_G (G : Ctx) (s : Sto) (x : Var) (T : Typ) (ds : Defs) :
  WfSto G s → Env.binds x (Val.val_new T ds) s → Env.binds x (Typ.typ_bnd T) G := by
  -- TODO
  sorry

theorem tight_bound_completeness (G : Ctx) (s : Sto) (x : Var) (T : Typ) (ds : Defs)
    (A : TypLabel) (S U : Typ) :
  WfSto G s → Env.binds x (Val.val_new T ds) s →
  TyTrm ty_general sub_tight G (Trm.trm_var (Avar.avar_f x)) (Typ.typ_rcd (Dec.dec_typ A S U)) →
  Subtyp ty_general sub_tight G (Typ.typ_sel (Avar.avar_f x) A) U ∧
  Subtyp ty_general sub_tight G S (Typ.typ_sel (Avar.avar_f x) A) := by
  -- TODO
  sorry

theorem all_intro_inversion (G : Ctx) (S : Typ) (t : Trm) (U : Typ) :
  TyTrm ty_precise sub_general G (Trm.trm_val (Val.val_lambda S t)) U → ∃ T, U = Typ.typ_all S T := by
  -- TODO
  sorry

theorem new_intro_inversion (G : Ctx) (T : Typ) (ds : Defs) (U : Typ) :
  TyTrm ty_precise sub_general G (Trm.trm_val (Val.val_new T ds)) U →
  U = Typ.typ_bnd T ∧ record_type T := by
  -- TODO
  sorry

-- Possible types closure (tight)

theorem possible_types_closure_tight (G : Ctx) (s : Sto) (x : Var) (v : Val) (T0 U0 : Typ) :
  WfSto G s → Env.binds x v s → PossibleTypes G x v T0 →
  Subtyp ty_general sub_tight G T0 U0 → PossibleTypes G x v U0 := by
  -- TODO
  sorry

-- Pieces and inversions for possible types

theorem ty_defs_has (G : Ctx) (ds : Defs) (T : Typ) (d : Defn) :
  TyDefs G ds T → defs_has ds d → record_type T → ∃ D, TyDef G d D ∧ RecordSub T (Typ.typ_rcd D) := by
  -- TODO
  sorry

theorem defs_has_hasnt_neq (ds : Defs) (d1 d2 : Defn) :
  defs_has ds d1 → defs_hasnt ds (label_of_def d2) → label_of_def d1 ≠ label_of_def d2 := by
  -- TODO
  sorry

theorem record_has_ty_defs (G : Ctx) (T : Typ) (ds : Defs) (D : Dec) :
  TyDefs G ds T → RecordHas T D → ∃ d, defs_has ds d ∧ TyDef G d D := by
  -- TODO
  sorry

theorem pt_piece_rcd (G : Ctx) (s : Sto) (x : Var) (T : Typ) (ds : Defs) (d : Defn) (D : Dec) :
  WfSto G s → Env.binds x (Val.val_new T ds) s → defs_has (open_defs x ds) d → TyDef G d D →
  PossibleTypes G x (Val.val_new T ds) (Typ.typ_rcd D) := by
  -- TODO
  sorry

theorem pt_rcd_has_piece (G : Ctx) (s : Sto) (x : Var) (T : Typ) (ds : Defs) (D : Dec) :
  WfSto G s → Env.binds x (Val.val_new T ds) s → RecordHas (open_typ x T) D →
  PossibleTypes G x (Val.val_new T ds) (Typ.typ_rcd D) := by
  -- TODO
  sorry

theorem pt_rcd_trm_inversion (G : Ctx) (s : Sto) (x : Var) (v : Val) (a : TrmLabel) (T : Typ) :
  WfSto G s → Env.binds x v s → PossibleTypes G x v (Typ.typ_rcd (Dec.dec_trm a T)) →
  ∃ S ds t, v = Val.val_new S ds ∧ defs_has (open_defs x ds) (Defn.def_trm a t) ∧ TyTrm ty_general sub_general G t T := by
  -- TODO
  sorry

theorem pt_rcd_typ_inversion (G : Ctx) (s : Sto) (x : Var) (v : Val) (A : TypLabel) (S U : Typ) :
  WfSto G s → Env.binds x v s → PossibleTypes G x v (Typ.typ_rcd (Dec.dec_typ A S U)) →
  ∃ T ds T', v = Val.val_new T ds ∧ defs_has (open_defs x ds) (Defn.def_typ A T') ∧
    Subtyp ty_general sub_general G S T' ∧ Subtyp ty_general sub_general G T' U := by
  -- TODO
  sorry

theorem record_sub_and (T T1 T2 : Typ) :
  record_type T → T = Typ.typ_and T1 T2 → RecordSub T T1 ∧ RecordSub T T2 := by
  -- TODO
  sorry

theorem record_sub_has (T1 T2 : Typ) (D : Dec) :
  RecordHas T2 D → RecordSub T1 T2 → RecordHas T1 D := by
  -- TODO
  sorry

theorem pt_record_sub_has (G : Ctx) (x : Var) (v : Val) (T1 T2 : Typ) :
  (∀ D, RecordHas T1 D → PossibleTypes G x v (Typ.typ_rcd D)) →
  RecordSub T1 T2 →
  (∀ D, RecordHas T2 D → PossibleTypes G x v (Typ.typ_rcd D)) := by
  -- TODO
  sorry

theorem pt_has_record (G : Ctx) (x : Var) (v : Val) (T : Typ) :
  (∀ D, RecordHas T D → PossibleTypes G x v (Typ.typ_rcd D)) →
  record_type T → PossibleTypes G x v T := by
  -- TODO
  sorry

theorem pt_has_sub (G : Ctx) (x : Var) (v : Val) (T U : Typ) :
  (∀ D, RecordHas T D → PossibleTypes G x v (Typ.typ_rcd D)) →
  record_type T → RecordSub T U → PossibleTypes G x v U := by
  -- TODO
  sorry

theorem possible_types_closure_record (G : Ctx) (s : Sto) (x : Var) (T : Typ) (ds : Defs) (U : Typ) :
  WfSto G s → Env.binds x (Val.val_new T ds) s → RecordSub (open_typ x T) U → PossibleTypes G x (Val.val_new T ds) U := by
  -- TODO
  sorry

theorem pt_and_inversion (G : Ctx) (s : Sto) (x : Var) (v : Val) (T1 T2 : Typ) :
  WfSto G s → Env.binds x v s → PossibleTypes G x v (Typ.typ_and T1 T2) →
  PossibleTypes G x v T1 ∧ PossibleTypes G x v T2 := by
  -- TODO
  sorry

-- Possible types completeness for values / tight / general

theorem possible_types_completeness_for_values (G : Ctx) (s : Sto) (x : Var) (v : Val) (T : Typ) :
  WfSto G s → Env.binds x v s → TyTrm ty_precise sub_general G (Trm.trm_val v) T → PossibleTypes G x v T := by
  -- TODO
  sorry

theorem possible_types_completeness_tight (G : Ctx) (s : Sto) (x : Var) (T : Typ) :
  WfSto G s → TyTrm ty_general sub_tight G (Trm.trm_var (Avar.avar_f x)) T → ∃ v, Env.binds x v s ∧ PossibleTypes G x v T := by
  -- TODO
  sorry

theorem possible_types_completeness (G : Ctx) (s : Sto) (x : Var) (T : Typ) :
  WfSto G s → TyTrm ty_general sub_general G (Trm.trm_var (Avar.avar_f x)) T → ∃ v, Env.binds x v s ∧ PossibleTypes G x v T := by
  -- TODO
  sorry

theorem possible_types_lemma (G : Ctx) (s : Sto) (x : Var) (v : Val) (T : Typ) :
  WfSto G s → Env.binds x v s → TyTrm ty_general sub_general G (Trm.trm_var (Avar.avar_f x)) T → PossibleTypes G x v T := by
  -- TODO
  sorry

theorem ctx_binds_to_sto_binds_typing (G : Ctx) (s : Sto) (x : Var) (T : Typ) :
  WfSto G s → Env.binds x T G → ∃ v, Env.binds x v s ∧ TyTrm ty_precise sub_general G (Trm.trm_val v) T := by
  -- TODO
  sorry

-- Basic helper lemmas

theorem var_new_typing (G : Ctx) (s : Sto) (x : Var) (T : Typ) (ds : Defs) :
  WfSto G s → Env.binds x (Val.val_new T ds) s →
  TyTrm ty_general sub_general G (Trm.trm_var (Avar.avar_f x)) (open_typ x T) := by
  -- TODO
  sorry

theorem new_ty_defs (G : Ctx) (s : Sto) (x : Var) (T : Typ) (ds : Defs) :
  WfSto G s → Env.binds x (Val.val_new T ds) s →
  TyDefs G (open_defs x ds) (open_typ x T) := by
  -- TODO
  sorry

theorem possible_types_closure (G : Ctx) (s : Sto) (x : Var) (v : Val) (S T : Typ) :
  WfSto G s → Env.binds x v s → PossibleTypes G x v S → Subtyp ty_general sub_general G S T → PossibleTypes G x v T := by
  -- TODO
  sorry

-- Canonical forms and safety

theorem canonical_forms_1 (G : Ctx) (s : Sto) (x : Var) (T U : Typ) :
  WfSto G s → TyTrm ty_general sub_general G (Trm.trm_var (Avar.avar_f x)) (Typ.typ_all T U) →
  ∃ (L : Vars) (T' : Typ) (t : Trm), Env.binds x (Val.val_lambda T' t) s ∧ Subtyp ty_general sub_general G T T' ∧
            (∀ y, y ∉ L → TyTrm ty_general sub_general ((y, T) :: G) (open_trm y t) (open_typ y U)) := by
  -- TODO
  sorry

theorem canonical_forms_2 (G : Ctx) (s : Sto) (x : Var) (a : TrmLabel) (T : Typ) :
  WfSto G s → TyTrm ty_general sub_general G (Trm.trm_var (Avar.avar_f x)) (Typ.typ_rcd (Dec.dec_trm a T)) →
  ∃ S ds t, Env.binds x (Val.val_new S ds) s ∧ TyDefs G (open_defs x ds) (open_typ x S) ∧ defs_has (open_defs x ds) (Defn.def_trm a t) ∧
             TyTrm ty_general sub_general G t T := by
  -- TODO
  sorry

theorem var_typing_implies_avar_f (G : Ctx) (a : Avar) (T : Typ) :
  TyTrm ty_general sub_general G (Trm.trm_var a) T → ∃ x, a = Avar.avar_f x := by
  -- TODO
  sorry

theorem val_typing (G : Ctx) (v : Val) (T : Typ) :
  TyTrm ty_general sub_general G (Trm.trm_val v) T →
  ∃ T', TyTrm ty_precise sub_general G (Trm.trm_val v) T' ∧ Subtyp ty_general sub_general G T' T := by
  -- TODO
  sorry

theorem safety (G : Ctx) (s : Sto) (t : Trm) (T : Typ) :
  WfSto G s → TyTrm ty_general sub_general G t T →
  (NormalForm t ∨ (∃ s' t' G' G'', Red t s t' s' ∧ G' = G ++ G'' ∧ TyTrm ty_general sub_general G' t' T ∧ WfSto G' s')) := by
  -- TODO
  sorry

end Lp2lc.Active.Dot_top_bot
