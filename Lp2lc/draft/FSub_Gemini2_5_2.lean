import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic

import Aesop
import Lean.Elab.Term
import Lean.Meta
-- Std.Data.Finset removed, relying on Mathlib.Data.Finset.Basic for ∅, ∪ etc.

open Lean Elab Term Meta

-- Rocq Line 15
inductive Typ where
  | typ_top   : Typ
  | typ_bvar  : Nat → Typ
  | typ_fvar  : String → Typ -- Assuming Coq's 'var' is represented as String
  | typ_arrow : Typ → Typ → Typ
  | typ_all   : Typ → Typ → Typ

-- Rocq Line 24
inductive Trm where
  | trm_bvar : Nat → Trm
  | trm_fvar : String → Trm -- Assuming Coq's 'var' is represented as String
  | trm_abs  : Typ → Trm → Trm
  | trm_app  : Trm → Trm → Trm
  | trm_tabs : Typ → Trm → Trm
  | trm_tapp : Trm → Typ → Trm

-- Rocq Line 34
def open_tt_rec (k : Nat) (u : Typ) (t : Typ) : Typ :=
  match t with
  | Typ.typ_top         => Typ.typ_top
  | Typ.typ_bvar j      => if k = j then u else (Typ.typ_bvar j)
  | Typ.typ_fvar x      => Typ.typ_fvar x
  | Typ.typ_arrow t1 t2 => Typ.typ_arrow (open_tt_rec k u t1) (open_tt_rec k u t2)
  | Typ.typ_all t1 t2   => Typ.typ_all (open_tt_rec k u t1) (open_tt_rec (k + 1) u t2)

-- Rocq Line 43
def open_tt (t : Typ) (u : Typ) : Typ := open_tt_rec 0 u t

-- Rocq Line 47
def open_te_rec (k : Nat) (u : Typ) (e : Trm) : Trm :=
  match e with
  | Trm.trm_bvar i    => Trm.trm_bvar i
  | Trm.trm_fvar x    => Trm.trm_fvar x
  | Trm.trm_abs v e1  => Trm.trm_abs  (open_tt_rec k u v)  (open_te_rec k u e1)
  | Trm.trm_app e1 e2 => Trm.trm_app  (open_te_rec k u e1) (open_te_rec k u e2)
  | Trm.trm_tabs v e1 => Trm.trm_tabs (open_tt_rec k u v)  (open_te_rec (k + 1) u e1)
  | Trm.trm_tapp e1 v => Trm.trm_tapp (open_te_rec k u e1) (open_tt_rec k u v)

-- Rocq Line 57
def open_te (t : Trm) (u : Typ) : Trm := open_te_rec 0 u t

-- Rocq Line 61
def open_ee_rec (k : Nat) (f_subst : Trm) (e_term : Trm) : Trm :=
  match e_term with
  | Trm.trm_bvar i      => if k = i then f_subst else (Trm.trm_bvar i)
  | Trm.trm_fvar x      => Trm.trm_fvar x
  | Trm.trm_abs v_type e1  => Trm.trm_abs v_type (open_ee_rec (k + 1) f_subst e1)
  | Trm.trm_app e1 e2   => Trm.trm_app (open_ee_rec k f_subst e1) (open_ee_rec k f_subst e2)
  | Trm.trm_tabs v_type e1 => Trm.trm_tabs v_type (open_ee_rec k f_subst e1)
  | Trm.trm_tapp e1 v_type => Trm.trm_tapp (open_ee_rec k f_subst e1) v_type

-- Rocq Line 71
def open_ee (t : Trm) (u : Trm) : Trm := open_ee_rec 0 u t

-- Rocq Line 75
notation:67 t " open_tt_var " x => open_tt t (Typ.typ_fvar x)

-- Rocq Line 76
notation:67 t " open_te_var " x => open_te t (Typ.typ_fvar x)

-- Rocq Line 77
notation:67 t " open_ee_var " x => open_ee t (Trm.trm_fvar x)

-- Rocq Line 81
inductive IsTyp : Typ → Prop where
  -- Rocq Line 82
  | top : IsTyp Typ.typ_top
  -- Rocq Line 84
  | var (x_var : String) : IsTyp (Typ.typ_fvar x_var)
  -- Rocq Line 86
  | arrow (t1 t2 : Typ) :
      IsTyp t1 →
      IsTyp t2 →
      IsTyp (Typ.typ_arrow t1 t2)
  -- Rocq Line 90
  | all_typ (l : List String) (t1 t2 : Typ) : -- Renamed 'all' to 'all_typ' to avoid conflict with Lean's 'all' keyword
      IsTyp t1 →
      (∀ (x_var : String), x_var ∉ l → IsTyp (t2 open_tt_var x_var)) →
      IsTyp (Typ.typ_all t1 t2)

-- Rocq Line 97
inductive IsTrm : Trm → Prop where
  -- Rocq Line 98
  | var (x_var : String) : IsTrm (Trm.trm_fvar x_var)
  -- Rocq Line 100
  | abs (l : List String) (v_type : Typ) (e1 : Trm) :
      IsTyp v_type →
      (∀ (x_var : String), x_var ∉ l → IsTrm (e1 open_ee_var x_var)) →
      IsTrm (Trm.trm_abs v_type e1)
  -- Rocq Line 104
  | app (e1 e2 : Trm) :
      IsTrm e1 →
      IsTrm e2 →
      IsTrm (Trm.trm_app e1 e2)
  -- Rocq Line 108
  | tabs (l : List String) (v_type : Typ) (e1 : Trm) :
      IsTyp v_type →
      (∀ (x_var : String), x_var ∉ l → IsTrm (e1 open_te_var x_var)) →
      IsTrm (Trm.trm_tabs v_type e1)
  -- Rocq Line 112
  | tapp (e1 : Trm) (v_type : Typ) :
      IsTrm e1 →
      IsTyp v_type →
      IsTrm (Trm.trm_tapp e1 v_type)

-- Rocq Line 121
inductive Binding where -- Renamed from Bind to avoid name collision
  -- Rocq Line 122
  | bind_sub : Typ → Binding
  -- Rocq Line 123
  | bind_typ : Typ → Binding

-- Rocq Line 125
notation:23 x " ~<: " t_typ => (x, Binding.bind_sub t_typ)

-- Rocq Line 127
notation:23 x " ~: " t_typ => (x, Binding.bind_typ t_typ)

-- Rocq Line 132
abbrev Env := List (String × Binding)

-- Rocq Line 139
inductive WfTyp : Env → Typ → Prop where
  -- Rocq Line 140
  | top (env : Env) : WfTyp env Typ.typ_top
  -- Rocq Line 142
  | var (u_bound : Typ) (env : Env) (x_var : String) :
      (x_var, Binding.bind_sub u_bound) ∈ env → -- Assuming 'binds' check membership
      WfTyp env (Typ.typ_fvar x_var)
  -- Rocq Line 145
  | arrow (env : Env) (t1 t2 : Typ) :
      WfTyp env t1 →
      WfTyp env t2 →
      WfTyp env (Typ.typ_arrow t1 t2)
  -- Rocq Line 149
  | all_form (l_fresh : List String) (env : Env) (t1 t2 : Typ) :
      WfTyp env t1 →
      (∀ (x_var : String), x_var ∉ l_fresh →
        WfTyp ((x_var, Binding.bind_sub t1) :: env) (t2 open_tt_var x_var)) →
      WfTyp env (Typ.typ_all t1 t2)

-- Rocq Line 159
inductive OkEnv : Env → Prop where
  -- Rocq Line 160
  | empty : OkEnv []
  -- Rocq Line 162
  | sub (env : Env) (var_name : String) (typ_val : Typ) :
      OkEnv env →
      WfTyp env typ_val →
      var_name ∉ env.map Prod.fst → -- 'var_name' is fresh for 'env'
      OkEnv ((var_name, Binding.bind_sub typ_val) :: env)
  -- Rocq Line 164
  | typ (env : Env) (var_name : String) (typ_val : Typ) :
      OkEnv env →
      WfTyp env typ_val →
      var_name ∉ env.map Prod.fst → -- 'var_name' is fresh for 'env'
      OkEnv ((var_name, Binding.bind_typ typ_val) :: env)

-- Rocq Line 169
inductive Subtyp : Env → Typ → Typ → Prop where
  -- Rocq Line 170
  | top (env : Env) (s : Typ) :
      OkEnv env →
      WfTyp env s →
      Subtyp env s Typ.typ_top
  -- Rocq Line 174
  | refl_tvar (env : Env) (x_var : String) :
      OkEnv env →
      WfTyp env (Typ.typ_fvar x_var) →
      Subtyp env (Typ.typ_fvar x_var) (Typ.typ_fvar x_var)
  -- Rocq Line 178
  | trans_tvar (u_bound : Typ) (env : Env) (t_super : Typ) (x_var : String) :
      (x_var, Binding.bind_sub u_bound) ∈ env →
      Subtyp env u_bound t_super →
      Subtyp env (Typ.typ_fvar x_var) t_super
  -- Rocq Line 182
  | arrow (env : Env) (s1 s2 t1 t2 : Typ) :
      Subtyp env t1 s1 →
      Subtyp env s2 t2 →
      Subtyp env (Typ.typ_arrow s1 s2) (Typ.typ_arrow t1 t2)
  -- Rocq Line 186
  | all_form (l_fresh : List String) (env : Env) (s1 s2 t1 t2 : Typ) :
      Subtyp env t1 s1 →
      (∀ (x_var : String), x_var ∉ l_fresh →
        Subtyp ((x_var, Binding.bind_sub t1) :: env) (s2 open_tt_var x_var) (t2 open_tt_var x_var)) →
      Subtyp env (Typ.typ_all s1 s2) (Typ.typ_all t1 t2)

-- Rocq Line 194
inductive Typing : Env → Trm → Typ → Prop where
  -- Rocq Line 195
  | typing_var (env : Env) (x_var : String) (t : Typ) :
      OkEnv env →
      (x_var, Binding.bind_typ t) ∈ env →
      Typing env (Trm.trm_fvar x_var) t
  -- Rocq Line 199
  | typing_abs (l_fresh : List String) (env : Env) (v_type : Typ) (e1 : Trm) (t1 : Typ) :
      (∀ (x_var : String), x_var ∉ l_fresh →
        Typing ((x_var, Binding.bind_typ v_type) :: env) (e1 open_ee_var x_var) t1) →
      Typing env (Trm.trm_abs v_type e1) (Typ.typ_arrow v_type t1)
  -- Rocq Line 203
  | typing_app (env : Env) (e1 e2 : Trm) (t1 t2 : Typ) :
      Typing env e1 (Typ.typ_arrow t1 t2) →
      Typing env e2 t1 →
      Typing env (Trm.trm_app e1 e2) t2
  -- Rocq Line 207
  | typing_tabs (l_fresh : List String) (env : Env) (v_type : Typ) (e1 : Trm) (t1 : Typ) :
      (∀ (x_var : String), x_var ∉ l_fresh →
        Typing ((x_var, Binding.bind_sub v_type) :: env) (e1 open_te_var x_var) (t1 open_tt_var x_var)) →
      Typing env (Trm.trm_tabs v_type e1) (Typ.typ_all v_type t1)
  -- Rocq Line 211
  | typing_tapp (env : Env) (e1 : Trm) (t_actual : Typ) (t1_of_all t2_of_all : Typ) :
      Typing env e1 (Typ.typ_all t1_of_all t2_of_all) →
      Subtyp env t_actual t1_of_all →
      Typing env (Trm.trm_tapp e1 t_actual) (open_tt t2_of_all t_actual)
  -- Rocq Line 215
  | typing_sub (env : Env) (e : Trm) (s_typ t_typ : Typ) :
      Typing env e s_typ →
      Subtyp env s_typ t_typ →
      Typing env e t_typ

-- Rocq Line 222
inductive Value : Trm → Prop where
  -- Rocq Line 223
  | value_abs (v_type : Typ) (e1_body : Trm) :
      Value (Trm.trm_abs v_type e1_body)
  -- Rocq Line 225
  | value_tabs (v_type : Typ) (e1_body : Trm) :
      Value (Trm.trm_tabs v_type e1_body)

-- Rocq Line 230
inductive Red : Trm → Trm → Prop where
  -- Rocq Line 231
  | red_app_1 (e1 e1_prime e2 : Trm) :
      Red e1 e1_prime →
      Red (Trm.trm_app e1 e2) (Trm.trm_app e1_prime e2)
  -- Rocq Line 235
  | red_app_2 (e1 e2 e2_prime : Trm) :
      Value e1 →
      Red e2 e2_prime →
      Red (Trm.trm_app e1 e2) (Trm.trm_app e1 e2_prime)
  -- Rocq Line 239
  | red_tapp (e1 e1_prime : Trm) (v_type_arg : Typ) :
      Red e1 e1_prime →
      Red (Trm.trm_tapp e1 v_type_arg) (Trm.trm_tapp e1_prime v_type_arg)
  -- Rocq Line 243
  | red_abs (v_type : Typ) (e1_body : Trm) (v2_arg : Trm) :
      Value v2_arg →
      Red (Trm.trm_app (Trm.trm_abs v_type e1_body) v2_arg) (open_ee e1_body v2_arg)
  -- Rocq Line 247
  | red_tabs (v1_type : Typ) (e1_body : Trm) (v2_type_arg : Typ) :
      Red (Trm.trm_tapp (Trm.trm_tabs v1_type e1_body) v2_type_arg) (open_te e1_body v2_type_arg)


-- attribute [aesop safe constructor] WfTyp OkEnv Subtyp Typing Value

-- Rocq Line 254
def Preservation : Prop :=
  ∀ (env : Env) (e_term e_prime_term : Trm) (t_type : Typ),
    Typing env e_term t_type →
    Red e_term e_prime_term →
    Typing env e_prime_term t_type

-- Rocq Line 259
def Progress : Prop :=
  ∀ (e_term : Trm) (t_type : Typ),
    Typing [] e_term t_type →
      Value e_term ∨ (∃ e_prime_term, Red e_term e_prime_term)

-- Rocq Line 273
def fv_tt (t : Typ) : Finset String :=
  match t with
  | Typ.typ_top         => ∅
  | Typ.typ_bvar _      => ∅
  | Typ.typ_fvar x      => {x}
  | Typ.typ_arrow t1 t2 => fv_tt t1 ∪ fv_tt t2
  | Typ.typ_all t1 t2   => fv_tt t1 ∪ fv_tt t2

-- Rocq Line 284
def fv_te (e_term : Trm) : Finset String :=
  match e_term with
  | Trm.trm_bvar _            => ∅
  | Trm.trm_fvar _            => ∅ -- Term fvars are not type fvars
  | Trm.trm_abs v_type e1_body  => fv_tt v_type ∪ fv_te e1_body
  | Trm.trm_app e1 e2           => fv_te e1 ∪ fv_te e2
  | Trm.trm_tabs v_type e1_body => fv_tt v_type ∪ fv_te e1_body
  | Trm.trm_tapp e1 v_type_arg  => fv_tt v_type_arg ∪ fv_te e1

-- Rocq Line 296
def fv_ee (e_term : Trm) : Finset String :=
  match e_term with
  | Trm.trm_bvar _            => ∅
  | Trm.trm_fvar x_var        => {x_var}
  | Trm.trm_abs _type_binder e1_body     => fv_ee e1_body
  | Trm.trm_app e1 e2           => fv_ee e1 ∪ fv_ee e2
  | Trm.trm_tabs _type_binder e1_body    => fv_ee e1_body
  | Trm.trm_tapp e1 _type_arg         => fv_ee e1

-- Rocq Line 308
def subst_tt (z_var_to_replace : String) (u_replacement_type : Typ) (t_target_type : Typ) : Typ :=
  match t_target_type with
  | Typ.typ_top                         => Typ.typ_top
  | Typ.typ_bvar j                      => Typ.typ_bvar j
  | Typ.typ_fvar x_var                  => if x_var = z_var_to_replace then u_replacement_type else Typ.typ_fvar x_var
  | Typ.typ_arrow t1 t2                 => Typ.typ_arrow (subst_tt z_var_to_replace u_replacement_type t1) (subst_tt z_var_to_replace u_replacement_type t2)
  | Typ.typ_all t1_binder t2_body       => Typ.typ_all (subst_tt z_var_to_replace u_replacement_type t1_binder) (subst_tt z_var_to_replace u_replacement_type t2_body)

-- Rocq Line 319
def subst_te (z_var_to_replace : String) (u_replacement_type : Typ) (e_target_term : Trm) : Trm :=
  match e_target_term with
  | Trm.trm_bvar i_idx                 => Trm.trm_bvar i_idx
  | Trm.trm_fvar x_var                 => Trm.trm_fvar x_var -- Type substitution doesn't affect term variables
  | Trm.trm_abs v_binder_type e1_body  => Trm.trm_abs (subst_tt z_var_to_replace u_replacement_type v_binder_type) (subst_te z_var_to_replace u_replacement_type e1_body)
  | Trm.trm_app e1 e2                  => Trm.trm_app (subst_te z_var_to_replace u_replacement_type e1) (subst_te z_var_to_replace u_replacement_type e2)
  | Trm.trm_tabs v_binder_type e1_body => Trm.trm_tabs (subst_tt z_var_to_replace u_replacement_type v_binder_type) (subst_te z_var_to_replace u_replacement_type e1_body)
  | Trm.trm_tapp e1 v_type_arg         => Trm.trm_tapp (subst_te z_var_to_replace u_replacement_type e1) (subst_tt z_var_to_replace u_replacement_type v_type_arg)

-- Rocq Line 331
def subst_ee (z_var_to_replace : String) (u_replacement_term : Trm) (e_target_term : Trm) : Trm :=
  match e_target_term with
  | Trm.trm_bvar i_idx                   => Trm.trm_bvar i_idx
  | Trm.trm_fvar x_var                   => if x_var = z_var_to_replace then u_replacement_term else Trm.trm_fvar x_var
  | Trm.trm_abs v_binder_type e1_body    => Trm.trm_abs v_binder_type (subst_ee z_var_to_replace u_replacement_term e1_body)
  | Trm.trm_app e1 e2                    => Trm.trm_app (subst_ee z_var_to_replace u_replacement_term e1) (subst_ee z_var_to_replace u_replacement_term e2)
  | Trm.trm_tabs v_binder_type e1_body   => Trm.trm_tabs v_binder_type (subst_ee z_var_to_replace u_replacement_term e1_body)
  | Trm.trm_tapp e1 v_type_arg           => Trm.trm_tapp (subst_ee z_var_to_replace u_replacement_term e1) v_type_arg

-- Rocq Line 343
def subst_tb (z_var_to_replace : String) (p_replacement_type : Typ) (b_target_binding : Binding) : Binding :=
  match b_target_binding with
  | Binding.bind_sub t_bound => Binding.bind_sub (subst_tt z_var_to_replace p_replacement_type t_bound)
  | Binding.bind_typ t_type  => Binding.bind_typ (subst_tt z_var_to_replace p_replacement_type t_type)

-- Corresponds to Coq's usage of 'dom x' for an env x in gather_vars (Rocq Line 368)
def dom (env : Env) : Finset String :=
  (env.map (fun entry => entry.1)).toFinset

-- -- Rocq Line 423
lemma open_tt_rec_type_core (T : Typ) :
  ∀ (j : Nat) (V U : Typ) (i : Nat),
  i ≠ j →
  (open_tt_rec j V T) = open_tt_rec i U (open_tt_rec j V T) →
  T = open_tt_rec i U T := by
  induction T with
  | typ_top =>
    intros j V U i h_neq h_eq_main
    simp only [open_tt_rec]
  | typ_bvar k_idx =>
    intros j V U i h_neq h_eq_main
    simp only [open_tt_rec] at h_eq_main -- Simplify h_eq_main first
    simp only [open_tt_rec]       -- Then simplify the goal
    by_cases h_j_eq_k_idx : j = k_idx
    · -- Case: j = k_idx
      subst h_j_eq_k_idx -- Substitute j with k_idx
      rw [if_pos rfl] at h_eq_main -- After subst, the if condition is k_idx = k_idx, which is true by rfl.
      simp [h_neq] -- Goal's if condition is i = k_idx; h_neq is i ≠ k_idx. simp should simplify this.
    · -- Case: j ≠ k_idx
      rw [if_neg h_j_eq_k_idx] at h_eq_main -- h_j_eq_k_idx is j ≠ k_idx. Simplifies LHS of h_eq_main.
      -- Now h_eq_main is: Typ.typ_bvar k_idx = open_tt_rec i U (Typ.typ_bvar k_idx)
      -- The goal is:        Typ.typ_bvar k_idx = (if k_idx = i then U else Typ.typ_bvar k_idx)
      -- These are definitionally equal.
      exact h_eq_main
  | typ_fvar x =>
    intros j V U i h_neq h_eq_main
    simp only [open_tt_rec]
  | typ_arrow T1 T2 ih1 ih2 =>
    intros j V U i h_neq h_eq_main
    simp only [open_tt_rec] at h_eq_main
    have h_inj := Typ.typ_arrow.inj h_eq_main
    simp only [open_tt_rec] -- Simplify RHS of main goal
    rw [← ih1 j V U i h_neq h_inj.1]
    rw [← ih2 j V U i h_neq h_inj.2]
  | typ_all S T_body ih_S ih_T_body =>
    intros j V U i h_neq h_eq_main
    simp only [open_tt_rec] at h_eq_main
    have h_inj := Typ.typ_all.inj h_eq_main
    have h_neq_plus_1 : (i+1) ≠ (j+1) := by intro hc; exact h_neq (Nat.add_right_cancel hc)
    simp only [open_tt_rec] -- Simplify RHS of main goal
    rw [← ih_S j V U i h_neq h_inj.1]
    rw [← ih_T_body (j+1) V U (i+1) h_neq_plus_1 h_inj.2]

#check open_tt_rec_type_core

-- This code assumes that types like `Lp2lc.Name`, `Lp2lc.Ast.Term`, `Lp2lc.Ast.Typ`, `Lp2lc.Ast.Env`
-- and functions like `Lp2lc.Ast.fv_te`, `Lp2lc.Ast.fv_tt`, `Lp2lc.Ast.dom` are in scope
-- (e.g., via `open Lp2lc` or if these definitions are made within `namespace Lp2lc`).
-- If not, you may need to qualify them (e.g., `Lp2lc.Name`).

-- TODO: Define Lp2lc.Ast.fv_ee : Lp2lc.Ast.Term → Finset Lp2lc.Name

/--
Corresponds to Ltac `gather_vars` from Rocq Fsub.v line 362.

This term elaborator constructs a Lean term of type `Finset Lp2lc.Name`.
It collects variables from hypotheses in the local context based on their types:
- Hypotheses of type `Finset Lp2lc.Name` (Coq `vars`) are included directly.
- For `h : Lp2lc.Name` (Coq `var`), it includes `{h}`.
- For `h : Lp2lc.Ast.Term` (Coq `trm`), it includes `Lp2lc.Ast.fv_te h` (and `Lp2lc.Ast.fv_ee h` if defined).
- For `h : Lp2lc.Ast.Typ` (Coq `typ`), it includes `Lp2lc.Ast.fv_tt h`.
- For `h : Lp2lc.Ast.Env` (Coq `env`), it includes `Lp2lc.Ast.dom h`.
The final result is a term representing the union of all these variable sets.

Usage in a tactic or another elaborator:
`let forbidden_names_term ← `(gatherVarsTerm)`
-- To get an Expr:
`let forbidden_names_expr ← elabTerm forbidden_names_term (some <expected_type_expr>)`
-- To evaluate to a Finset Lp2lc.Name (requires care, typically in MetaM):
-- `let forbidden_names_value ← evalExpr (Finset Lp2lc.Name) forbidden_names_expr`
-/
syntax "gatherVarsTerm" : term

@[term_elab «gatherVarsTerm»]
def elabGatherVarsTerm : TermElab := fun stx expectedType? => do
  -- Assuming Lp2lc.Name is the type for variables.
  let nameTypeIdent := mkIdent ``Lp2lc.Name

  let mut collectedSetTerms : List Term := []
  let lctx ← getLCtx
  for ld in lctx do
    if ld.isImplementationDetail then continue

    let hypIdent := mkIdent ld.userName
    let hypTypeExpr := ld.type

    -- Helper for checking `Finset X`
    let isFinsetOf (typeExpr : Expr) (targetElementType : Name) : MetaM Bool := do
      if typeExpr.isAppOfArity ``Finset 1 then
        let argType := typeExpr.getAppArgs[0]!
        -- Check if argType is definitionally equal to targetElementType
        let targetElementExpr ← elabTerm (mkIdent targetElementType) none
        return ← isDefEq argType targetElementExpr
      return false

    if ← isFinsetOf hypTypeExpr ``Lp2lc.Name then
      collectedSetTerms := hypIdent :: collectedSetTerms
    else if (← inferType hypIdent).isConstOf ``Lp2lc.Name then -- More direct check for Name type
      collectedSetTerms := (← `(Finset.singleton $hypIdent)) :: collectedSetTerms
    else if (← inferType hypIdent).isConstOf ``Lp2lc.Ast.Term then
      collectedSetTerms := (← `(Lp2lc.Ast.fv_te $hypIdent)) :: collectedSetTerms
      -- TODO: Uncomment and implement when Lp2lc.Ast.fv_ee is defined
      -- collectedSetTerms := (← `(Lp2lc.Ast.fv_ee $hypIdent)) :: collectedSetTerms
    else if (← inferType hypIdent).isConstOf ``Lp2lc.Ast.Typ then
      collectedSetTerms := (← `(Lp2lc.Ast.fv_tt $hypIdent)) :: collectedSetTerms
    else if (← inferType hypIdent).isConstOf ``Lp2lc.Ast.Env then
      collectedSetTerms := (← `(Lp2lc.Ast.dom $hypIdent)) :: collectedSetTerms
    -- Add more conditions if other types need to be handled

  let emptySetTerm ← `((∅ : Finset $nameTypeIdent))
  let finalSetTerm ← collectedSetTerms.foldlM (fun acc nextTerm => `($acc ∪ $nextTerm)) emptySetTerm

  -- Ensure the final term has the expected type (e.g., Finset Lp2lc.Name)
  let expectedFinsetNameTypeExpr ← elabTerm (← `(Finset $nameTypeIdent)) none
  elabTerm finalSetTerm (some expectedFinsetNameTypeExpr)


/--
Helper function to evaluate an expression representing a `Finset Lean.Name`.
This is marked `unsafe` because `evalExpr` can execute arbitrary code if the expression is complex.
It also requires `Inhabited (Finset Lean.Name)`, which is true since `Lean.Name` is `Inhabited`.
-/
unsafe def evalFinsetLeanNameExpr (expr : Expr) : MetaM (Finset Lean.Name) :=
  evalExpr (Finset Lean.Name) expr

/--
Pure function to generate a fresh `Lean.Name` given a set of forbidden names and a base name.
Tries `baseName`, then `baseName_0`, `baseName_1`, ...
-/
partial def generateFreshLeanName (forbiddenNames : Finset Lean.Name) (baseName : Lean.Name) : Lean.Name :=
  let rec findFresh (idx : Nat) : Lean.Name :=
    let currentName := baseName.mkNum idx -- Creates names like `baseName.0`, `baseName.1`
    if currentName ∈ forbiddenNames then
      findFresh (idx + 1)
    else
      currentName
  if baseName ∈ forbiddenNames then
    findFresh 0 -- Start with baseName_0 if baseName itself is taken
  else
    baseName -- Base name itself is fresh and preferred

/--
Corresponds to Ltac `pick_fresh x` from Rocq Fsub.v line 369.
`pick_fresh x` is `let L := gather_vars in (pick_fresh_gen L x)`.
This term elaborator computes a fresh `Lean.Name`.

Usage in a tactic or another elaborator:
`let fresh_name_term ← `(pickFreshName% x_base)`
-- To get an Expr of the fresh name:
`let fresh_name_expr ← elabTerm fresh_name_term (some <expected_Lean.Name_type_expr>)`
-- To get the actual Lean.Name value (e.g. in MetaM):
-- `let name_val ← evalExpr Lean.Name fresh_name_expr` (but direct computation as below is better)

Assumes `Lp2lc.Name` (from `gatherVarsTerm`'s output type `Finset Lp2lc.Name`) is `Lean.Name`.
If `Lp2lc.Name` is a custom type, `evalFinsetLeanNameExpr` would need to expect `Finset Lp2lc.Name`
and `generateFreshLeanName` would operate on `Lp2lc.Name` (requiring `.mkNum` equivalent).
-/
syntax "pfn " baseNameToken:ident : term

@[term_elab pfn]
def elabPickFreshName : TermElab := fun stx expectedType? => do
  match stx with
  | `(pfn $baseIdent) =>
    let baseLeanName := baseIdent.raw.getId -- baseIdent is TSyntax `ident, .raw gives Syntax, .getId gets Name

    -- 1. Get the term for the set of forbidden names
    let forbiddenSetTermSyntax ← `(gatherVarsTerm)

    -- 2. Elaborate this term to get an Expr.
    -- Assuming gatherVarsTerm produces Finset Lp2lc.Name, and Lp2lc.Name is Lean.Name.
    let finsetLeanNameTypeExpr ← elabTerm (← `(Finset Lean.Name)) none
    let forbiddenSetExpr ← elabTerm forbiddenSetTermSyntax (some finsetLeanNameTypeExpr)

    -- 3. Evaluate the expression to get the actual Finset Lean.Name value.
    let forbiddenNamesValue : Finset Lean.Name ← unsafe evalFinsetLeanNameExpr forbiddenSetExpr

    -- 4. Generate the fresh Lean.Name.
    let freshNameValue := generateFreshLeanName forbiddenNamesValue baseLeanName

    -- 5. Convert the resulting Lean.Name back into a term (an identifier).
    let freshNameSyntax := mkIdent freshNameValue

    -- Elaborate this identifier syntax to an Expr, ensuring it's typed as Lean.Name
    -- (or Lp2lc.Name if that's the standard type for names in this context).
    let expectedNameTypeExpr ← elabTerm (mkIdent ``Lean.Name) none -- Or ``Lp2lc.Name if preferred as output type
    elabTerm freshNameSyntax (some expectedNameTypeExpr)
  | _ => throwUnsupportedSyntax
