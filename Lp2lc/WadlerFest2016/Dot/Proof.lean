import «Lp2lc».Active.DOT.Def
import «Lp2lc».Active.DOT.Auxiliary

namespace Lp2lc.Active.DOT

-- Scaffolds for Dot lemmas and theorems. Do not introduce axioms; use sorry.
-- We will populate this file in original Coq order, each with a Coq line comment.

-- Theorems scaffolded from Coq Dot.v, in original order. All proofs use sorry unless trivial.

-- [Coq: Dot.v line 391]
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

-- Opening and records

-- [Coq: Dot.v line 1320]
/-- Opening a declaration preserves its Label. -/
@[simp] theorem open_dec_preserves_label (D : Dec) (x : Var) (i : Nat) :
  label_of_dec D = label_of_dec (open_rec_dec i x D) := by
  -- TODO: by cases D; simp
  sorry

-- [Coq: Dot.v line 1326]
/-- Opening a record declaration yields a record declaration. -/
@[simp] theorem open_record_dec (D : Dec) (x : Var) :
  RecordDec D → RecordDec (open_dec x D) := by
  -- TODO: by cases D
  intro _; sorry

-- [Coq: Dot.v line 1332]
/-- Opening a record type preserves its record shape and labels. -/
@[simp] theorem open_record_typ (T : Typ) (x : Var) (ls : Finset Label) :
  RecordTyp T ls → RecordTyp (open_typ x T) ls := by
  -- TODO: by induction on RecordTyp
  intro _; sorry

-- [Coq: Dot.v line 1451]
/-- Opening preserves the record_type predicate. -/
@[simp] theorem open_record_type (T : Typ) (x : Var) :
  record_type T → record_type (open_typ x T) := by
  intro h
  rcases h with ⟨ls, hrt⟩
  exact ⟨ls, open_record_typ T x ls hrt⟩

-- [Coq: Dot.v line 1458]
/-- Reverse: if open_typ x T is a record, then T is a record (under freshness in Coq proof). -/
 theorem open_record_type_rev (T : Typ) (x : Var) :
  record_type (open_typ x T) → record_type T := by
  -- TODO: requires open_eq lemmas; keep as scaffold
  intro _; sorry

-- [Coq: Dot.v line 1465]
/-- The Label of a well-typed def matches the Label of its derived declaration. -/
@[simp] theorem label_same_typing {G : Ctx} {d : Defn} {D : Dec} :
  TyDef G d D → label_of_def d = label_of_dec D := by
  intro h; cases h <;> rfl

-- Substitution effects on labels

-- [Coq: Dot.v line 956]
@[simp] theorem subst_label_of_dec (x y : Var) (D : Dec) :
  label_of_dec D = label_of_dec (Subst.subst_dec x y D) := by
  -- TODO: trivial by cases
  sorry

-- [Coq: Dot.v line 962]
@[simp] theorem subst_label_of_def (x y : Var) (d : Defn) :
  label_of_def d = label_of_def (Subst.subst_def x y d) := by
  -- TODO: trivial by cases
  sorry

-- Has-member family scaffolds and key lemmas (statements only; proofs TODO)

-- [Coq: Dot.v line 1987]
/-- Inversion for HasMemberRules constructors. -/
theorem has_member_rules_inv (G : Ctx) (x : Var) (T : Typ) (A : TypLabel) (S U : Typ) :
  HasMemberRules G x T A S U →
  (T = Typ.typ_rcd (Dec.dec_typ A S U)) ∨
  (∃ T1 T2, T = Typ.typ_and T1 T2 ∧ (HasMember G x T1 A S U ∨ HasMember G x T2 A S U)) ∨
  (∃ T', T = Typ.typ_bnd T' ∧ HasMember G x (open_typ x T') A S U) ∨
  (∃ y B T', T = Typ.typ_sel (Avar.avar_f y) B ∧
              TyTrm ty_precise sub_general G (Trm.trm_var (Avar.avar_f y)) (Typ.typ_rcd (Dec.dec_typ B T' T')) ∧
              HasMember G x T' A S U) := by
  intro _; sorry

-- [Coq: Dot.v line 2006]
/-- Inversion for HasMember via has_member_rules_inv. -/
theorem has_member_inv (G : Ctx) (x : Var) (T : Typ) (A : TypLabel) (S U : Typ) :
  HasMember G x T A S U →
  (T = Typ.typ_rcd (Dec.dec_typ A S U)) ∨
  (∃ T1 T2, T = Typ.typ_and T1 T2 ∧ (HasMember G x T1 A S U ∨ HasMember G x T2 A S U)) ∨
  (∃ T', T = Typ.typ_bnd T' ∧ HasMember G x (open_typ x T') A S U) ∨
  (∃ y B T', T = Typ.typ_sel (Avar.avar_f y) B ∧
              TyTrm ty_precise sub_general G (Trm.trm_var (Avar.avar_f y)) (Typ.typ_rcd (Dec.dec_typ B T' T')) ∧
              HasMember G x T' A S U) := by
  intro h; cases h with
  | has_any _ _ _ _ _ _ hty hrules => exact has_member_rules_inv _ _ _ _ _ _ hrules

-- Core store/Value lemmas and possible types (precise signatures, proofs deferred)

-- [Coq: Dot.v line 2020]
/-- If x maps to a new-object Value in the store, it checks against typ_bnd of its shape. -/
theorem val_new_typing
  (G : Ctx) (s : Sto) (x : Var) (T : Typ) (ds : Defs) :
  WfSto G s → Env.binds x (Val.val_new T ds) s →
  TyTrm ty_precise sub_general G (Trm.trm_val (Val.val_new T ds)) (Typ.typ_bnd T) := by
  intro _ _; sorry

-- [Coq: Dot.v line 2040]
/-- In a record type {A: S..U} reachable from T, bounds coincide. -/
theorem rcd_typ_eq_bounds (T : Typ) (A : TypLabel) (S U : Typ) :
  record_type T →
  RecordSub T (Typ.typ_rcd (Dec.dec_typ A S U)) →
  S = U := by
  intro _ _; sorry

-- [Coq: Dot.v line 2053] (split into two)
/-- From HasMember, extract the corresponding RecordSub judgement. -/
theorem has_member_rcd_typ_sub
  (G : Ctx) (x : Var) (T : Typ) (A : TypLabel) (S U : Typ) :
  HasMember G x T A S U → record_type T → RecordSub T (Typ.typ_rcd (Dec.dec_typ A S U)) := by
  intro _ _; sorry

/-- From HasMemberRules, extract the corresponding RecordSub judgement. -/
theorem has_member_rules_rcd_typ_sub
  (G : Ctx) (x : Var) (T : Typ) (A : TypLabel) (S U : Typ) :
  HasMemberRules G x T A S U → record_type T → RecordSub T (Typ.typ_rcd (Dec.dec_typ A S U)) := by
  intro _ _; sorry

-- [Coq: Dot.v line 2075]
/-- Tightness: if HasMember holds at a recursive type x: T, its bounds are equal. -/
theorem has_member_tightness
  (G : Ctx) (s : Sto) (x : Var) (T : Typ) (ds : Defs)
  (A : TypLabel) (S U : Typ) :
  WfSto G s → Env.binds x (Val.val_new T ds) s →
  HasMember G x (Typ.typ_bnd T) A S U →
  S = U := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2098]
/-- Covariance of HasMember under subtyping and Typing. -/
theorem has_member_covariance
  (G : Ctx) (s : Sto) (T1 T2 : Typ) (x : Var) (A : TypLabel) (S2 U2 : Typ) :
  WfSto G s →
  Subtyp ty_general sub_tight G T1 T2 →
  TyTrm ty_general sub_tight G (Trm.trm_var (Avar.avar_f x)) T1 →
  HasMember G x T2 A S2 U2 →
  ∃ S1 U1, HasMember G x T1 A S1 U1 ∧
           Subtyp ty_general sub_tight G S2 S1 ∧
           Subtyp ty_general sub_tight G U1 U2 := by
  intro _ _ _ _; sorry

-- [Coq: Dot.v line 2172]
/-- Monotonicity: from HasMember at T, derive at typ_bnd T0 under a store binding. -/
theorem has_member_monotonicity
  (G : Ctx) (s : Sto) (x : Var) (T0 : Typ) (ds : Defs)
  (T : Typ) (A : TypLabel) (S U : Typ) :
  WfSto G s → Env.binds x (Val.val_new T0 ds) s → HasMember G x T A S U →
  ∃ T1, HasMember G x (Typ.typ_bnd T0) A T1 T1 ∧
        Subtyp ty_general sub_tight G S T1 ∧ Subtyp ty_general sub_tight G T1 U := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2232] (split into two)
/-- HasMember either is reflexive on a record or subtypes to that record (Value). -/
theorem has_member_rcd_typ_sub2
  (G : Ctx) (x : Var) (T : Typ) (A : TypLabel) (S U : Typ) :
  HasMember G x T A S U → record_type T →
  T = (Typ.typ_rcd (Dec.dec_typ A S U)) ∨ Subtyp ty_precise sub_general G T (Typ.typ_rcd (Dec.dec_typ A S U)) := by
  intro _ _; sorry

/-- HasMemberRules either is reflexive on a record or subtypes to that record. -/
theorem has_member_rules_rcd_typ_sub2
  (G : Ctx) (x : Var) (T : Typ) (A : TypLabel) (S U : Typ) :
  HasMemberRules G x T A S U → record_type T →
  T = (Typ.typ_rcd (Dec.dec_typ A S U)) ∨ Subtyp ty_precise sub_general G T (Typ.typ_rcd (Dec.dec_typ A S U)) := by
  intro _ _; sorry

-- [Coq: Dot.v line 2257]
/-- If x is bound to new T ds in s and WfSto, then Γ Has x : typ_bnd T. -/
theorem wf_sto_val_new_in_G (G : Ctx) (s : Sto) (x : Var) (T : Typ) (ds : Defs) :
  WfSto G s → Env.binds x (Val.val_new T ds) s → Env.binds x (Typ.typ_bnd T) G := by
  intro _ _; sorry

-- [Coq: Dot.v line 2276]
/-- Tight bound completeness for selections on x. -/
theorem tight_bound_completeness
  (G : Ctx) (s : Sto) (x : Var) (T : Typ) (ds : Defs)
  (A : TypLabel) (S U : Typ) :
  WfSto G s → Env.binds x (Val.val_new T ds) s →
  TyTrm ty_general sub_tight G (Trm.trm_var (Avar.avar_f x)) (Typ.typ_rcd (Dec.dec_typ A S U)) →
  Subtyp ty_general sub_tight G (Typ.typ_sel (Avar.avar_f x) A) U ∧
  Subtyp ty_general sub_tight G S (Typ.typ_sel (Avar.avar_f x) A) := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2328]
/-- Inversion for Typing of val_lambda under ty_precise. -/
theorem all_intro_inversion (G : Ctx) (S : Typ) (t : Trm) (U : Typ) :
  TyTrm ty_precise sub_general G (Trm.trm_val (Val.val_lambda S t)) U → ∃ T, U = Typ.typ_all S T := by
  intro _; sorry

-- [Coq: Dot.v line 2338]
/-- Inversion for Typing of val_new under ty_precise. -/
theorem new_intro_inversion (G : Ctx) (T : Typ) (ds : Defs) (U : Typ) :
  TyTrm ty_precise sub_general G (Trm.trm_val (Val.val_new T ds)) U → U = Typ.typ_bnd T ∧ record_type T := by
  intro _; sorry

-- [Coq: Dot.v line 2398]
/-- If x maps to new T ds in s, then Γ ⊢ x : open_typ x T. -/
theorem var_new_typing (G : Ctx) (s : Sto) (x : Var) (T : Typ) (ds : Defs) :
  WfSto G s → Env.binds x (Val.val_new T ds) s →
  TyTrm ty_general sub_general G (Trm.trm_var (Avar.avar_f x)) (open_typ x T) := by
  intro _ _; sorry

-- [Coq: Dot.v line 2407]
/-- From TyDefs and record_type, pick a D matching ds and show RecordSub. -/
theorem ty_defs_has (G : Ctx) (ds : Defs) (T : Typ) (d : Defn) :
  TyDefs G ds T → defs_has ds d → record_type T →
  ∃ D, TyDef G d D ∧ RecordSub T (Typ.typ_rcd D) := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2431]
/-- From the binding x = new T ds and a component Typing, show Ts piece for records. -/
theorem pt_rcd_has_piece (G : Ctx) (s : Sto) (x : Var) (T : Typ) (ds : Defs) (D : Dec) :
  WfSto G s → Env.binds x (Val.val_new T ds) s → RecordHas (open_typ x T) D →
  PossibleTypes G x (Val.val_new T ds) (Typ.typ_rcd D) := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2505]
/-- Inversion for a record field piece in Ts. -/
theorem pt_rcd_trm_inversion (G : Ctx) (s : Sto) (x : Var) (v : Val) (a : TrmLabel) (T : Typ) :
  WfSto G s → Env.binds x v s → PossibleTypes G x v (Typ.typ_rcd (Dec.dec_trm a T)) →
  ∃ S ds t, v = Val.val_new S ds ∧ defs_has (open_defs x ds) (Defn.def_trm a t) ∧ TyTrm ty_general sub_general G t T := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2517]
/-- Inversion for a record type piece in Ts. -/
theorem pt_rcd_typ_inversion (G : Ctx) (s : Sto) (x : Var) (v : Val) (A : TypLabel) (S U : Typ) :
  WfSto G s → Env.binds x v s → PossibleTypes G x v (Typ.typ_rcd (Dec.dec_typ A S U)) →
  ∃ T ds T', v = Val.val_new T ds ∧ defs_has (open_defs x ds) (Defn.def_typ A T') ∧
             Subtyp ty_general sub_general G S T' ∧ Subtyp ty_general sub_general G T' U := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2559]
/-- If T is a record type and T = T1 & T2, then RecordSub T T1 and RecordSub T T2. -/
theorem record_sub_and (T T1 T2 : Typ) :
  record_type T → T = Typ.typ_and T1 T2 → RecordSub T T1 ∧ RecordSub T T2 := by
  intro _ _; sorry

-- [Coq: Dot.v line 2603]
/-- RecordSub is compatible with RecordHas: if T1 ≤ T2, then any Dec in T2 is in T1. -/
theorem record_sub_has (T1 T2 : Typ) (D : Dec) :
  RecordHas T2 D → RecordSub T1 T2 → RecordHas T1 D := by
  intro _ _; sorry

-- [Coq: Dot.v line 2615]
/-- Closure of PossibleTypes under RecordSub of record-Has mapping. -/
theorem pt_record_sub_has (G : Ctx) (x : Var) (v : Val) (T1 T2 : Typ) :
  (∀ D, RecordHas T1 D → PossibleTypes G x v (Typ.typ_rcd D)) → RecordSub T1 T2 →
  (∀ D, RecordHas T2 D → PossibleTypes G x v (Typ.typ_rcd D)) := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2629]
/-- From per-declaration membership, build full PossibleTypes for a record type. -/
theorem pt_has_record (G : Ctx) (x : Var) (v : Val) (T : Typ) :
  (∀ D, RecordHas T D → PossibleTypes G x v (Typ.typ_rcd D)) → record_type T → PossibleTypes G x v T := by
  intro _ _; sorry

-- [Coq: Dot.v line 2637]
/-- From per-declaration membership and RecordSub, obtain PossibleTypes for U. -/
theorem pt_has_sub (G : Ctx) (x : Var) (v : Val) (T U : Typ) :
  (∀ D, RecordHas T D → PossibleTypes G x v (Typ.typ_rcd D)) →
  record_type T → RecordSub T U → PossibleTypes G x v U := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2650]
/-- Closure of PossibleTypes for x: new T ds and any U ≤ open_typ x T. -/
theorem possible_types_closure_record
  (G : Ctx) (s : Sto) (x : Var) (T U : Typ) (ds : Defs) :
  WfSto G s → Env.binds x (Val.val_new T ds) s → RecordSub (open_typ x T) U →
  PossibleTypes G x (Val.val_new T ds) U := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2671]
/-- Inversion of Ts entry for an intersection type. -/
theorem pt_and_inversion (G : Ctx) (s : Sto) (x : Var) (v : Val) (T1 T2 : Typ) :
  WfSto G s → Env.binds x v s → PossibleTypes G x v (Typ.typ_and T1 T2) →
  PossibleTypes G x v T1 ∧ PossibleTypes G x v T2 := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2702]
/-- Closure of Ts under tight subtyping. -/
theorem possible_types_closure_tight
  (G : Ctx) (s : Sto) (x : Var) (v : Val) (T0 U0 : Typ) :
  WfSto G s → Env.binds x v s → PossibleTypes G x v T0 → Subtyp ty_general sub_tight G T0 U0 →
  PossibleTypes G x v U0 := by
  intro _ _ _ _; sorry

-- [Coq: Dot.v line 2781]
/-- Completeness of Ts for precise Typing of v. -/
theorem possible_types_completeness_for_values
  (G : Ctx) (s : Sto) (x : Var) (v : Val) (T : Typ) :
  WfSto G s → Env.binds x v s → TyTrm ty_precise sub_general G (Trm.trm_val v) T →
  PossibleTypes G x v T := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2806]
/-- Completeness of Ts for tight Typing of x. -/
theorem possible_types_completeness_tight
  (G : Ctx) (s : Sto) (x : Var) (T : Typ) :
  WfSto G s → TyTrm ty_general sub_tight G (Trm.trm_var (Avar.avar_f x)) T →
  ∃ v, Env.binds x v s ∧ PossibleTypes G x v T := by
  intro _ _; sorry

-- [Coq: Dot.v line 2816]
/-- Completeness of Ts for general Typing of x. -/
theorem possible_types_completeness
  (G : Ctx) (s : Sto) (x : Var) (T : Typ) :
  WfSto G s → TyTrm ty_general sub_general G (Trm.trm_var (Avar.avar_f x)) T →
  ∃ v, Env.binds x v s ∧ PossibleTypes G x v T := by
  intro _ _; sorry

-- [Coq: Dot.v line 2846]
/-- Auxiliary lemma: from Γ, s ⊢ x : T and s(x) = v, we can conclude Ts item. -/
theorem possible_types_lemma
  (G : Ctx) (s : Sto) (x : Var) (v : Val) (T : Typ) :
  WfSto G s → Env.binds x v s → TyTrm ty_general sub_general G (Trm.trm_var (Avar.avar_f x)) T →
  PossibleTypes G x v T := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2857]
/-- From Γ ⊢ x : T and WfSto, extract a Value Typing and a store binding. -/
theorem ctx_binds_to_sto_binds_typing
  (G : Ctx) (s : Sto) (x : Var) (T : Typ) :
  WfSto G s → Env.binds x T G → ∃ v, Env.binds x v s ∧ TyTrm ty_precise sub_general G (Trm.trm_val v) T := by
  intro _ _; sorry

-- [Coq: Dot.v line 2935]
/-- Canonical forms 1 for all-types. -/
theorem canonical_forms_1
  (G : Ctx) (s : Sto) (x : Var) (T U : Typ) :
  WfSto G s → TyTrm ty_general sub_general G (Trm.trm_var (Avar.avar_f x)) (Typ.typ_all T U) →
  ∃ (L : Vars) (T' : Typ) (t : Trm), Env.binds x (Val.val_lambda T' t) s ∧ Subtyp ty_general sub_general G T T' ∧
    (∀ (y : Var), y ∉ L → TyTrm ty_general sub_general ((y, T) :: G) (open_trm y t) (open_typ y U)) := by
  intro _ _; sorry

-- [Coq: Dot.v line 2948]
/-- Canonical forms 2 for records. -/
theorem canonical_forms_2
  (G : Ctx) (s : Sto) (x : Var) (a : TrmLabel) (T : Typ) :
  WfSto G s → TyTrm ty_general sub_general G (Trm.trm_var (Avar.avar_f x)) (Typ.typ_rcd (Dec.dec_trm a T)) →
  ∃ (S : Typ) (ds : Defs) (t : Trm), Env.binds x (Val.val_new S ds) s ∧ TyDefs G (open_defs x ds) (open_typ x S) ∧
    defs_has (open_defs x ds) (Defn.def_trm a t) ∧ TyTrm ty_general sub_general G t T := by
  intro _ _; sorry

-- [Coq: Dot.v lines 3044, 3058]
/-- Induction principle over NormalForm: provide cases for variable and Value forms. -/
theorem normal_form_ind
  (P : Trm → Prop)
  (h_var : ∀ x, P (Trm.trm_var x))
  (h_val : ∀ v, P (Trm.trm_val v)) :
  ∀ t, NormalForm t → P t := by
  intro t h
  cases h with
  | nf_var x => exact h_var x
  | nf_val v => exact h_val v

/-- Safety: either t is a normal form, or it can step and remain well-typed under some extended store/context. -/
theorem safety
  (G : Ctx) (s : Sto) (t : Trm) (T : Typ) :
  WfSto G s →
  TyTrm ty_general sub_general G t T →
  NormalForm t ∨ ∃ t' s',
   Red t s t' s' ∧ ∃ G',
    TyTrm ty_general sub_general G' t' T ∧ WfSto G' s'
     := by
  intro _ _; sorry

end Lp2lc.Active.DOT
