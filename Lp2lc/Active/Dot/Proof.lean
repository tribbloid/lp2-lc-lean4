import «Lp2lc».Active.Dot.Def
import «Lp2lc».Active.Dot.Auxiliary

namespace Lp2lc.Active.Dot

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
/-- Opening a declaration preserves its label. -/ 
@[simp] theorem open_dec_preserves_label (D : dec) (x : Var) (i : Nat) :
  label_of_dec D = label_of_dec (open_rec_dec i x D) := by
  -- TODO: by cases D; simp
  sorry

-- [Coq: Dot.v line 1326]
/-- Opening a record declaration yields a record declaration. -/ 
@[simp] theorem open_record_dec (D : dec) (x : Var) :
  record_dec D → record_dec (open_dec x D) := by
  -- TODO: by cases D
  intro _; sorry

-- [Coq: Dot.v line 1332]
/-- Opening a record type preserves its record shape and labels. -/ 
@[simp] theorem open_record_typ (T : typ) (x : Var) (ls : Finset label) :
  record_typ T ls → record_typ (open_typ x T) ls := by
  -- TODO: by induction on record_typ
  intro _; sorry

-- [Coq: Dot.v line 1451]
/-- Opening preserves the record_type predicate. -/
@[simp] theorem open_record_type (T : typ) (x : Var) :
  record_type T → record_type (open_typ x T) := by
  intro h
  rcases h with ⟨ls, hrt⟩
  exact ⟨ls, open_record_typ T x ls hrt⟩

-- [Coq: Dot.v line 1458]
/-- Reverse: if open_typ x T is a record, then T is a record (under freshness in Coq proof). -/
 theorem open_record_type_rev (T : typ) (x : Var) :
  record_type (open_typ x T) → record_type T := by
  -- TODO: requires open_eq lemmas; keep as scaffold
  intro _; sorry

-- [Coq: Dot.v line 1465]
/-- The label of a well-typed def matches the label of its derived declaration. -/
@[simp] theorem label_same_typing {G : ctx} {d : defn} {D : dec} :
  ty_def G d D → label_of_def d = label_of_dec D := by
  intro h; cases h <;> rfl

-- Substitution effects on labels

-- [Coq: Dot.v line 956]
@[simp] theorem subst_label_of_dec (x y : Var) (D : dec) :
  label_of_dec D = label_of_dec (Subst.subst_dec x y D) := by
  -- TODO: trivial by cases
  sorry

-- [Coq: Dot.v line 962]
@[simp] theorem subst_label_of_def (x y : Var) (d : defn) :
  label_of_def d = label_of_def (Subst.subst_def x y d) := by
  -- TODO: trivial by cases
  sorry

-- Has-member family scaffolds and key lemmas (statements only; proofs TODO)

-- [Coq: Dot.v line 1987]
/-- Inversion for has_member_rules constructors. -/
theorem has_member_rules_inv (G : ctx) (x : Var) (T : typ) (A : typ_label) (S U : typ) :
  has_member_rules G x T A S U →
  (T = typ.typ_rcd (dec.dec_typ A S U)) ∨
  (∃ T1 T2, T = typ.typ_and T1 T2 ∧ (has_member G x T1 A S U ∨ has_member G x T2 A S U)) ∨
  (∃ T', T = typ.typ_bnd T' ∧ has_member G x (open_typ x T') A S U) ∨
  (∃ y B T', T = typ.typ_sel (avar.avar_f y) B ∧
              ty_trm ty_precise sub_general G (trm.trm_var (avar.avar_f y)) (typ.typ_rcd (dec.dec_typ B T' T')) ∧
              has_member G x T' A S U) := by
  intro _; sorry

-- [Coq: Dot.v line 2006]
/-- Inversion for has_member via has_member_rules_inv. -/
theorem has_member_inv (G : ctx) (x : Var) (T : typ) (A : typ_label) (S U : typ) :
  has_member G x T A S U →
  (T = typ.typ_rcd (dec.dec_typ A S U)) ∨
  (∃ T1 T2, T = typ.typ_and T1 T2 ∧ (has_member G x T1 A S U ∨ has_member G x T2 A S U)) ∨
  (∃ T', T = typ.typ_bnd T' ∧ has_member G x (open_typ x T') A S U) ∨
  (∃ y B T', T = typ.typ_sel (avar.avar_f y) B ∧
              ty_trm ty_precise sub_general G (trm.trm_var (avar.avar_f y)) (typ.typ_rcd (dec.dec_typ B T' T')) ∧
              has_member G x T' A S U) := by
  intro h; cases h with
  | has_any _ _ _ _ _ _ hty hrules => exact has_member_rules_inv _ _ _ _ _ _ hrules

-- Core store/value lemmas and possible types (precise signatures, proofs deferred)

-- [Coq: Dot.v line 2020]
/-- If x maps to a new-object value in the store, it checks against typ_bnd of its shape. -/
theorem val_new_typing
  (G : ctx) (s : sto) (x : Var) (T : typ) (ds : defs) :
  wf_sto G s → Env.binds x (val.val_new T ds) s →
  ty_trm ty_precise sub_general G (trm.trm_val (val.val_new T ds)) (typ.typ_bnd T) := by
  intro _ _; sorry

-- [Coq: Dot.v line 2040]
/-- In a record type {A: S..U} reachable from T, bounds coincide. -/
theorem rcd_typ_eq_bounds (T : typ) (A : typ_label) (S U : typ) :
  record_type T →
  record_sub T (typ.typ_rcd (dec.dec_typ A S U)) →
  S = U := by
  intro _ _; sorry

-- [Coq: Dot.v line 2053] (split into two)
/-- From has_member, extract the corresponding record_sub judgement. -/
theorem has_member_rcd_typ_sub
  (G : ctx) (x : Var) (T : typ) (A : typ_label) (S U : typ) :
  has_member G x T A S U → record_type T → record_sub T (typ.typ_rcd (dec.dec_typ A S U)) := by
  intro _ _; sorry

/-- From has_member_rules, extract the corresponding record_sub judgement. -/
theorem has_member_rules_rcd_typ_sub
  (G : ctx) (x : Var) (T : typ) (A : typ_label) (S U : typ) :
  has_member_rules G x T A S U → record_type T → record_sub T (typ.typ_rcd (dec.dec_typ A S U)) := by
  intro _ _; sorry

-- [Coq: Dot.v line 2075]
/-- Tightness: if has_member holds at a recursive type x: T, its bounds are equal. -/
theorem has_member_tightness
  (G : ctx) (s : sto) (x : Var) (T : typ) (ds : defs)
  (A : typ_label) (S U : typ) :
  wf_sto G s → Env.binds x (val.val_new T ds) s →
  has_member G x (typ.typ_bnd T) A S U →
  S = U := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2098]
/-- Covariance of has_member under subtyping and typing. -/
theorem has_member_covariance
  (G : ctx) (s : sto) (T1 T2 : typ) (x : Var) (A : typ_label) (S2 U2 : typ) :
  wf_sto G s →
  subtyp ty_general sub_tight G T1 T2 →
  ty_trm ty_general sub_tight G (trm.trm_var (avar.avar_f x)) T1 →
  has_member G x T2 A S2 U2 →
  ∃ S1 U1, has_member G x T1 A S1 U1 ∧
           subtyp ty_general sub_tight G S2 S1 ∧
           subtyp ty_general sub_tight G U1 U2 := by
  intro _ _ _ _; sorry

-- [Coq: Dot.v line 2172]
/-- Monotonicity: from has_member at T, derive at typ_bnd T0 under a store binding. -/
theorem has_member_monotonicity
  (G : ctx) (s : sto) (x : Var) (T0 : typ) (ds : defs)
  (T : typ) (A : typ_label) (S U : typ) :
  wf_sto G s → Env.binds x (val.val_new T0 ds) s → has_member G x T A S U →
  ∃ T1, has_member G x (typ.typ_bnd T0) A T1 T1 ∧
        subtyp ty_general sub_tight G S T1 ∧ subtyp ty_general sub_tight G T1 U := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2232] (split into two)
/-- has_member either is reflexive on a record or subtypes to that record (value). -/
theorem has_member_rcd_typ_sub2
  (G : ctx) (x : Var) (T : typ) (A : typ_label) (S U : typ) :
  has_member G x T A S U → record_type T →
  T = (typ.typ_rcd (dec.dec_typ A S U)) ∨ subtyp ty_precise sub_general G T (typ.typ_rcd (dec.dec_typ A S U)) := by
  intro _ _; sorry

/-- has_member_rules either is reflexive on a record or subtypes to that record. -/
theorem has_member_rules_rcd_typ_sub2
  (G : ctx) (x : Var) (T : typ) (A : typ_label) (S U : typ) :
  has_member_rules G x T A S U → record_type T →
  T = (typ.typ_rcd (dec.dec_typ A S U)) ∨ subtyp ty_precise sub_general G T (typ.typ_rcd (dec.dec_typ A S U)) := by
  intro _ _; sorry

-- [Coq: Dot.v line 2257]
/-- If x is bound to new T ds in s and wf_sto, then Γ has x : typ_bnd T. -/
theorem wf_sto_val_new_in_G (G : ctx) (s : sto) (x : Var) (T : typ) (ds : defs) :
  wf_sto G s → Env.binds x (val.val_new T ds) s → Env.binds x (typ.typ_bnd T) G := by
  intro _ _; sorry

-- [Coq: Dot.v line 2276]
/-- Tight bound completeness for selections on x. -/
theorem tight_bound_completeness
  (G : ctx) (s : sto) (x : Var) (T : typ) (ds : defs)
  (A : typ_label) (S U : typ) :
  wf_sto G s → Env.binds x (val.val_new T ds) s →
  ty_trm ty_general sub_tight G (trm.trm_var (avar.avar_f x)) (typ.typ_rcd (dec.dec_typ A S U)) →
  subtyp ty_general sub_tight G (typ.typ_sel (avar.avar_f x) A) U ∧
  subtyp ty_general sub_tight G S (typ.typ_sel (avar.avar_f x) A) := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2328]
/-- Inversion for typing of val_lambda under ty_precise. -/
theorem all_intro_inversion (G : ctx) (S : typ) (t : trm) (U : typ) :
  ty_trm ty_precise sub_general G (trm.trm_val (val.val_lambda S t)) U → ∃ T, U = typ.typ_all S T := by
  intro _; sorry

-- [Coq: Dot.v line 2338]
/-- Inversion for typing of val_new under ty_precise. -/
theorem new_intro_inversion (G : ctx) (T : typ) (ds : defs) (U : typ) :
  ty_trm ty_precise sub_general G (trm.trm_val (val.val_new T ds)) U → U = typ.typ_bnd T ∧ record_type T := by
  intro _; sorry

-- [Coq: Dot.v line 2398]
/-- If x maps to new T ds in s, then Γ ⊢ x : open_typ x T. -/
theorem var_new_typing (G : ctx) (s : sto) (x : Var) (T : typ) (ds : defs) :
  wf_sto G s → Env.binds x (val.val_new T ds) s →
  ty_trm ty_general sub_general G (trm.trm_var (avar.avar_f x)) (open_typ x T) := by
  intro _ _; sorry

-- [Coq: Dot.v line 2407]
/-- From ty_defs and record_type, pick a D matching ds and show record_sub. -/
theorem ty_defs_has (G : ctx) (ds : defs) (T : typ) (d : defn) :
  ty_defs G ds T → defs_has ds d → record_type T →
  ∃ D, ty_def G d D ∧ record_sub T (typ.typ_rcd D) := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2431]
/-- From the binding x = new T ds and a component typing, show Ts piece for records. -/
theorem pt_rcd_has_piece (G : ctx) (s : sto) (x : Var) (T : typ) (ds : defs) (D : dec) :
  wf_sto G s → Env.binds x (val.val_new T ds) s → record_has (open_typ x T) D →
  possible_types G x (val.val_new T ds) (typ.typ_rcd D) := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2505]
/-- Inversion for a record field piece in Ts. -/
theorem pt_rcd_trm_inversion (G : ctx) (s : sto) (x : Var) (v : val) (a : trm_label) (T : typ) :
  wf_sto G s → Env.binds x v s → possible_types G x v (typ.typ_rcd (dec.dec_trm a T)) →
  ∃ S ds t, v = val.val_new S ds ∧ defs_has (open_defs x ds) (defn.def_trm a t) ∧ ty_trm ty_general sub_general G t T := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2517]
/-- Inversion for a record type piece in Ts. -/
theorem pt_rcd_typ_inversion (G : ctx) (s : sto) (x : Var) (v : val) (A : typ_label) (S U : typ) :
  wf_sto G s → Env.binds x v s → possible_types G x v (typ.typ_rcd (dec.dec_typ A S U)) →
  ∃ T ds T', v = val.val_new T ds ∧ defs_has (open_defs x ds) (defn.def_typ A T') ∧
             subtyp ty_general sub_general G S T' ∧ subtyp ty_general sub_general G T' U := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2559]
/-- If T is a record type and T = T1 & T2, then record_sub T T1 and record_sub T T2. -/
theorem record_sub_and (T T1 T2 : typ) :
  record_type T → T = typ.typ_and T1 T2 → record_sub T T1 ∧ record_sub T T2 := by
  intro _ _; sorry

-- [Coq: Dot.v line 2603]
/-- record_sub is compatible with record_has: if T1 ≤ T2, then any dec in T2 is in T1. -/
theorem record_sub_has (T1 T2 : typ) (D : dec) :
  record_has T2 D → record_sub T1 T2 → record_has T1 D := by
  intro _ _; sorry

-- [Coq: Dot.v line 2615]
/-- Closure of possible_types under record_sub of record-has mapping. -/
theorem pt_record_sub_has (G : ctx) (x : Var) (v : val) (T1 T2 : typ) :
  (∀ D, record_has T1 D → possible_types G x v (typ.typ_rcd D)) → record_sub T1 T2 →
  (∀ D, record_has T2 D → possible_types G x v (typ.typ_rcd D)) := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2629]
/-- From per-declaration membership, build full possible_types for a record type. -/
theorem pt_has_record (G : ctx) (x : Var) (v : val) (T : typ) :
  (∀ D, record_has T D → possible_types G x v (typ.typ_rcd D)) → record_type T → possible_types G x v T := by
  intro _ _; sorry

-- [Coq: Dot.v line 2637]
/-- From per-declaration membership and record_sub, obtain possible_types for U. -/
theorem pt_has_sub (G : ctx) (x : Var) (v : val) (T U : typ) :
  (∀ D, record_has T D → possible_types G x v (typ.typ_rcd D)) →
  record_type T → record_sub T U → possible_types G x v U := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2650]
/-- Closure of possible_types for x: new T ds and any U ≤ open_typ x T. -/
theorem possible_types_closure_record
  (G : ctx) (s : sto) (x : Var) (T U : typ) (ds : defs) :
  wf_sto G s → Env.binds x (val.val_new T ds) s → record_sub (open_typ x T) U →
  possible_types G x (val.val_new T ds) U := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2671]
/-- Inversion of Ts entry for an intersection type. -/
theorem pt_and_inversion (G : ctx) (s : sto) (x : Var) (v : val) (T1 T2 : typ) :
  wf_sto G s → Env.binds x v s → possible_types G x v (typ.typ_and T1 T2) →
  possible_types G x v T1 ∧ possible_types G x v T2 := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2702]
/-- Closure of Ts under tight subtyping. -/
theorem possible_types_closure_tight
  (G : ctx) (s : sto) (x : Var) (v : val) (T0 U0 : typ) :
  wf_sto G s → Env.binds x v s → possible_types G x v T0 → subtyp ty_general sub_tight G T0 U0 →
  possible_types G x v U0 := by
  intro _ _ _ _; sorry

-- [Coq: Dot.v line 2781]
/-- Completeness of Ts for precise typing of v. -/
theorem possible_types_completeness_for_values
  (G : ctx) (s : sto) (x : Var) (v : val) (T : typ) :
  wf_sto G s → Env.binds x v s → ty_trm ty_precise sub_general G (trm.trm_val v) T →
  possible_types G x v T := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2806]
/-- Completeness of Ts for tight typing of x. -/
theorem possible_types_completeness_tight
  (G : ctx) (s : sto) (x : Var) (T : typ) :
  wf_sto G s → ty_trm ty_general sub_tight G (trm.trm_var (avar.avar_f x)) T →
  ∃ v, Env.binds x v s ∧ possible_types G x v T := by
  intro _ _; sorry

-- [Coq: Dot.v line 2816]
/-- Completeness of Ts for general typing of x. -/
theorem possible_types_completeness
  (G : ctx) (s : sto) (x : Var) (T : typ) :
  wf_sto G s → ty_trm ty_general sub_general G (trm.trm_var (avar.avar_f x)) T →
  ∃ v, Env.binds x v s ∧ possible_types G x v T := by
  intro _ _; sorry

-- [Coq: Dot.v line 2846]
/-- Auxiliary lemma: from Γ, s ⊢ x : T and s(x) = v, we can conclude Ts item. -/
theorem possible_types_lemma
  (G : ctx) (s : sto) (x : Var) (v : val) (T : typ) :
  wf_sto G s → Env.binds x v s → ty_trm ty_general sub_general G (trm.trm_var (avar.avar_f x)) T →
  possible_types G x v T := by
  intro _ _ _; sorry

-- [Coq: Dot.v line 2857]
/-- From Γ ⊢ x : T and wf_sto, extract a value typing and a store binding. -/
theorem ctx_binds_to_sto_binds_typing
  (G : ctx) (s : sto) (x : Var) (T : typ) :
  wf_sto G s → Env.binds x T G → ∃ v, Env.binds x v s ∧ ty_trm ty_precise sub_general G (trm.trm_val v) T := by
  intro _ _; sorry

-- [Coq: Dot.v line 2935]
/-- Canonical forms 1 for all-types. -/
theorem canonical_forms_1
  (G : ctx) (s : sto) (x : Var) (T U : typ) :
  wf_sto G s → ty_trm ty_general sub_general G (trm.trm_var (avar.avar_f x)) (typ.typ_all T U) →
  ∃ (L : Vars) (T' : typ) (t : trm), Env.binds x (val.val_lambda T' t) s ∧ subtyp ty_general sub_general G T T' ∧
    (∀ (y : Var), y ∉ L → ty_trm ty_general sub_general ((y, T) :: G) (open_trm y t) (open_typ y U)) := by
  intro _ _; sorry

-- [Coq: Dot.v line 2948]
/-- Canonical forms 2 for records. -/
theorem canonical_forms_2
  (G : ctx) (s : sto) (x : Var) (a : trm_label) (T : typ) :
  wf_sto G s → ty_trm ty_general sub_general G (trm.trm_var (avar.avar_f x)) (typ.typ_rcd (dec.dec_trm a T)) →
  ∃ (S : typ) (ds : defs) (t : trm), Env.binds x (val.val_new S ds) s ∧ ty_defs G (open_defs x ds) (open_typ x S) ∧
    defs_has (open_defs x ds) (defn.def_trm a t) ∧ ty_trm ty_general sub_general G t T := by
  intro _ _; sorry

-- [Coq: Dot.v lines 3044, 3058]
/-- Induction principle over normal_form: provide cases for variable and value forms. -/
theorem normal_form_ind
  (P : trm → Prop)
  (h_var : ∀ x, P (trm.trm_var x))
  (h_val : ∀ v, P (trm.trm_val v)) :
  ∀ t, normal_form t → P t := by
  intro t h
  cases h with
  | nf_var x => exact h_var x
  | nf_val v => exact h_val v

/-- Safety: either t is a normal form, or it can step and remain well-typed under some extended store/context. -/
theorem safety
  (G : ctx) (s : sto) (t : trm) (T : typ) :
  wf_sto G s →
  ty_trm ty_general sub_general G t T →
  normal_form t ∨ ∃ t' s',
   red t s t' s' ∧ ∃ G',
    ty_trm ty_general sub_general G' t' T ∧ wf_sto G' s'
     := by
  intro _ _; sorry

end Lp2lc.Active.Dot
