/-***************************************************************************
* Preservation and Progress for System-F with Subtyping - Definitions      *
* Brian Aydemir & Arthur Charguéraud, March 2007                           *
***************************************************************************-/

import Std
import Mathlib.Data.Finset.Basic
import Aesop

namespace Lp2lc.Active

-- line 49
structure Var where
  name : String
  deriving Repr, BEq, Hashable, DecidableEq

abbrev Vars := Finset Var

-- line 17
inductive typ : Type where
  | typ_top   : typ
  | typ_bvar  : Nat -> typ
  | typ_fvar  : Var -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_all   : typ -> typ -> typ

-- line 26
inductive trm : Type where
  | trm_bvar : Nat -> trm
  | trm_fvar : Var -> trm
  | trm_abs  : typ -> trm -> trm
  | trm_app  : trm -> trm -> trm
  | trm_tabs : typ -> trm -> trm
  | trm_tapp : trm -> typ -> trm

-- line 36
def open_tt_rec (K : Nat) (U : typ) (T : typ) : typ :=
  match T with
  | typ.typ_top         => typ.typ_top
  | typ.typ_bvar J      => if K = J then U else (typ.typ_bvar J)
  | typ.typ_fvar X      => typ.typ_fvar X
  | typ.typ_arrow T1 T2 => typ.typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ.typ_all T1 T2   => typ.typ_all (open_tt_rec K U T1) (open_tt_rec (K + 1) U T2)

-- line 45
def open_tt (T : typ) (U : typ) : typ := open_tt_rec 0 U T

-- line 49
def open_te_rec (K : Nat) (U : typ) (e : trm) : trm :=
  match e with
  | trm.trm_bvar i    => trm.trm_bvar i
  | trm.trm_fvar x    => trm.trm_fvar x
  | trm.trm_abs V e1  => trm.trm_abs  (open_tt_rec K U V)  (open_te_rec K U e1)
  | trm.trm_app e1 e2 => trm.trm_app  (open_te_rec K U e1) (open_te_rec K U e2)
  | trm.trm_tabs V e1 => trm.trm_tabs (open_tt_rec K U V)  (open_te_rec (K + 1) U e1)
  | trm.trm_tapp e1 V => trm.trm_tapp (open_te_rec K U e1) (open_tt_rec K U V)

-- line 59
def open_te (t : trm) (U : typ) : trm := open_te_rec 0 U t

-- line 63
def open_ee_rec (k : Nat) (f : trm) (e : trm) : trm :=
  match e with
  | trm.trm_bvar i    => if k = i then f else (trm.trm_bvar i)
  | trm.trm_fvar x    => trm.trm_fvar x
  | trm.trm_abs V e1  => trm.trm_abs V (open_ee_rec (k + 1) f e1)
  | trm.trm_app e1 e2 => trm.trm_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | trm.trm_tabs V e1 => trm.trm_tabs V (open_ee_rec k f e1)
  | trm.trm_tapp e1 V => trm.trm_tapp (open_ee_rec k f e1) V

-- line 73
def open_ee (t : trm) (u : trm) : trm := open_ee_rec 0 u t

-- line 77
notation:67 T " open_tt_var " X => open_tt T (typ.typ_fvar X)
-- line 78
notation:67 t " open_te_var " X => open_te t (typ.typ_fvar X)
-- line 79
notation:67 t " open_ee_var " x => open_ee t (trm.trm_fvar x)

-- line 83
inductive def_type : typ -> Prop where
  | type_top :
      def_type typ.typ_top
  | type_var : (X : Var) ->
      def_type (typ.typ_fvar X)
  | type_arrow : (T1 T2 : typ) ->
      def_type T1 ->
      def_type T2 ->
      def_type (typ.typ_arrow T1 T2)
  | type_all : (L : Vars) -> (T1 T2 : typ) ->
      def_type T1 ->
      (∀ (X : Var), X ∉ L -> def_type (T2 open_tt_var X)) ->
      def_type (typ.typ_all T1 T2)

-- line 99
inductive def_term : trm -> Prop where
  | term_var : (x : Var) ->
      def_term (trm.trm_fvar x)
  | term_abs : (L : Vars) -> (V : typ) -> (e1 : trm) ->
      def_type V ->
      (∀ (x : Var), x ∉ L -> def_term (e1 open_ee_var x)) ->
      def_term (trm.trm_abs V e1)
  | term_app : (e1 e2 : trm) ->
      def_term e1 ->
      def_term e2 ->
      def_term (trm.trm_app e1 e2)
  | term_tabs : (L : Vars) -> (V : typ) -> (e1 : trm) ->
      def_type V ->
      (∀ (X : Var), X ∉ L -> def_term (e1 open_te_var X)) ->
      def_term (trm.trm_tabs V e1)
  | term_tapp : (e1 : trm) -> (V : typ) ->
      def_term e1 ->
      def_type V ->
      def_term (trm.trm_tapp e1 V)

-- line 123
inductive bind : Type where
  | bind_sub : typ -> bind
  | bind_typ : typ -> bind

-- line 133
abbrev env := List (Var × bind)

-- line 134
def dom (E : env) : Vars := E.map (·.1) |>.toFinset

-- from LibLN
-- line 145
def binds (x : Var) (b : bind) (E : env) : Prop := E.lookup x = some b

-- line 140
inductive wft : env -> typ -> Prop where
  | wft_top : (E : env) ->
      wft E typ.typ_top
  | wft_var : (U : typ) -> (E : env) -> (X : Var) ->
      binds X (bind.bind_sub U) E ->
      wft E (typ.typ_fvar X)
  | wft_arrow : (E : env) -> (T1 T2 : typ) ->
      wft E T1 ->
      wft E T2 ->
      wft E (typ.typ_arrow T1 T2)
  | wft_all : (L : Vars) -> (E : env) -> (T1 T2 : typ) ->
      wft E T1 ->
      (∀ (X : Var), X ∉ L ->
        wft ((X, bind.bind_sub T1) :: E) (T2 open_tt_var X)) ->
      wft E (typ.typ_all T1 T2)

-- placeholder
-- line 200
axiom ok : env -> Prop

-- Axiom: there is always a variable fresh from a finite set.
axiom var_fresh : (L : Vars) -> ∃ X : Var, X ∉ L

-- line 161
inductive okt : env -> Prop where
  | okt_empty :
      okt []
  | okt_sub : (E : env) -> (X : Var) -> (T : typ) ->
      okt E -> wft E T -> E.lookup X = none -> okt ((X, bind.bind_sub T) :: E)
  | okt_typ : (E : env) -> (x : Var) -> (T : typ) ->
      okt E -> wft E T -> E.lookup x = none -> okt ((x, bind.bind_typ T) :: E)

-- line 169
inductive sub : env -> typ -> typ -> Prop where
  | sub_top : (E : env) -> (S : typ) ->
      okt E ->
      wft E S ->
      sub E S typ.typ_top
  | sub_refl_tvar : (E : env) -> (X : Var) ->
      okt E ->
      wft E (typ.typ_fvar X) ->
      sub E (typ.typ_fvar X) (typ.typ_fvar X)
  | sub_trans_tvar : (U : typ) -> (E : env) -> (T : typ) -> (X : Var) ->
      binds X (bind.bind_sub U) E ->
      sub E U T ->
      sub E (typ.typ_fvar X) T
  | sub_arrow : (E : env) -> (S1 S2 T1 T2 : typ) ->
      sub E T1 S1 ->
      sub E S2 T2 ->
      sub E (typ.typ_arrow S1 S2) (typ.typ_arrow T1 T2)
  | sub_all : (L : Vars) -> (E : env) -> (S1 S2 T1 T2 : typ) ->
      sub E T1 S1 ->
      (∀ (X : Var), X ∉ L ->
          sub ((X, bind.bind_sub T1) :: E) (S2 open_tt_var X) (T2 open_tt_var X)) ->
      sub E (typ.typ_all S1 S2) (typ.typ_all T1 T2)

-- line 195
inductive typing : env -> trm -> typ -> Prop where
  | typing_var : (E : env) -> (x : Var) -> (T : typ) ->
      okt E ->
      binds x (bind.bind_typ T) E ->
      typing E (trm.trm_fvar x) T
  | typing_abs : (L : Vars) -> (E : env) -> (V : typ) -> (e1 : trm) -> (T1 : typ) ->
      (∀ (x : Var), x ∉ L ->
        typing ((x, bind.bind_typ V) :: E) (e1 open_ee_var x) T1) ->
      typing E (trm.trm_abs V e1) (typ.typ_arrow V T1)
  | typing_app : (T1 : typ) -> (E : env) -> (e1 e2 : trm) -> (T2 : typ) ->
      typing E e1 (typ.typ_arrow T1 T2) ->
      typing E e2 T1 ->
      typing E (trm.trm_app e1 e2) T2
  | typing_tabs : (L : Vars) -> (E : env) -> (V : typ) -> (e1 : trm) -> (T1 : typ) ->
      (∀ (X : Var), X ∉ L ->
        typing ((X, bind.bind_sub V) :: E) (e1 open_te_var X) (T1 open_tt_var X)) ->
      typing E (trm.trm_tabs V e1) (typ.typ_all V T1)
  | typing_tapp : (T1 : typ) -> (E : env) -> (e1 : trm) -> (T T2 : typ) ->
      typing E e1 (typ.typ_all T1 T2) ->
      sub E T T1 ->
      typing E (trm.trm_tapp e1 T) (open_tt T2 T)
  | typing_sub : (S : typ) -> (E : env) -> (e : trm) -> (T : typ) ->
      typing E e S ->
      sub E S T ->
      typing E e T

-- line 223
inductive value : trm -> Prop where
  | value_abs  : (V : typ) -> (e1 : trm) -> def_term (trm.trm_abs V e1) ->
                 value (trm.trm_abs V e1)
  | value_tabs : (V : typ) -> (e1 : trm) -> def_term (trm.trm_tabs V e1) ->
                 value (trm.trm_tabs V e1)

-- line 231
inductive red : trm -> trm -> Prop where
  | red_app_1 : (e1 e1' e2 : trm) ->
      def_term e2 ->
      red e1 e1' ->
      red (trm.trm_app e1 e2) (trm.trm_app e1' e2)
  | red_app_2 : (e1 e2 e2' : trm) ->
      value e1 ->
      red e2 e2' ->
      red (trm.trm_app e1 e2) (trm.trm_app e1 e2')
  | red_tapp : (e1 e1' : trm) -> (V : typ) ->
      def_type V ->
      red e1 e1' ->
      red (trm.trm_tapp e1 V) (trm.trm_tapp e1' V)
  | red_abs : (V : typ) -> (e1 : trm) -> (v2 : trm) ->
      def_term (trm.trm_abs V e1) ->
      value v2 ->
      red (trm.trm_app (trm.trm_abs V e1) v2) (open_ee e1 v2)
  | red_tabs : (V1 : typ) -> (e1 : trm) -> (V2 : typ) ->
      def_term (trm.trm_tabs V1 e1) ->
      def_type V2 ->
      red (trm.trm_tapp (trm.trm_tabs V1 e1) V2) (open_te e1 V2)

-- line 256
def preservation : Prop := ∀ (E : env) (e e' : trm) (T : typ),
  typing E e T ->
  red e e' ->
  typing E e' T

-- line 260
def progress : Prop := ∀ (e : trm) (T : typ),
  typing [] e T ->
  value e ∨ (∃ e', red e e')

-- line 275
def fv_tt (T : typ) : Vars :=
  match T with
  | typ.typ_top         => ∅
  | typ.typ_bvar _      => ∅
  | typ.typ_fvar X      => {X}
  | typ.typ_arrow T1 T2 => (fv_tt T1) ∪ (fv_tt T2)
  | typ.typ_all T1 T2   => (fv_tt T1) ∪ (fv_tt T2)

-- line 286
def fv_te (e : trm) : Vars :=
  match e with
  | trm.trm_bvar _    => ∅
  | trm.trm_fvar _    => ∅
  | trm.trm_abs V e1  => (fv_tt V) ∪ (fv_te e1)
  | trm.trm_app e1 e2 => (fv_te e1) ∪ (fv_te e2)
  | trm.trm_tabs V e1 => (fv_tt V) ∪ (fv_te e1)
  | trm.trm_tapp e1 V => (fv_tt V) ∪ (fv_te e1)

-- line 298
def fv_ee (e : trm) : Vars :=
  match e with
  | trm.trm_bvar _    => ∅
  | trm.trm_fvar x    => {x}
  | trm.trm_abs _ e1  => (fv_ee e1)
  | trm.trm_app e1 e2 => (fv_ee e1) ∪ (fv_ee e2)
  | trm.trm_tabs _ e1 => (fv_ee e1)
  | trm.trm_tapp e1 _ => (fv_ee e1)

-- line 310
def subst_tt (Z : Var) (U : typ) (T : typ) : typ :=
  match T with
  | typ.typ_top         => typ.typ_top
  | typ.typ_bvar J      => typ.typ_bvar J
  | typ.typ_fvar X      => by
      classical
      exact (if h : X = Z then (by simpa [h] using U) else typ.typ_fvar X)
  | typ.typ_arrow T1 T2 => typ.typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ.typ_all T1 T2   => typ.typ_all (subst_tt Z U T1) (subst_tt Z U T2)

-- line 321
def subst_te (Z : Var) (U : typ) (e : trm) : trm :=
  match e with
  | trm.trm_bvar i    => trm.trm_bvar i
  | trm.trm_fvar x    => trm.trm_fvar x
  | trm.trm_abs V e1  => trm.trm_abs  (subst_tt Z U V)  (subst_te Z U e1)
  | trm.trm_app e1 e2 => trm.trm_app  (subst_te Z U e1) (subst_te Z U e2)
  | trm.trm_tabs V e1 => trm.trm_tabs (subst_tt Z U V)  (subst_te Z U e1)
  | trm.trm_tapp e1 V => trm.trm_tapp (subst_te Z U e1) (subst_tt Z U V)

-- line 333
def subst_ee (z : Var) (u : trm) (e : trm) : trm :=
  match e with
  | trm.trm_bvar i    => trm.trm_bvar i
  | trm.trm_fvar x    => by
      classical
      exact (if h : x = z then (by simpa [h] using u) else trm.trm_fvar x)
  | trm.trm_abs V e1  => trm.trm_abs V (subst_ee z u e1)
  | trm.trm_app e1 e2 => trm.trm_app (subst_ee z u e1) (subst_ee z u e2)
  | trm.trm_tabs V e1 => trm.trm_tabs V (subst_ee z u e1)
  | trm.trm_tapp e1 V => trm.trm_tapp (subst_ee z u e1) V

-- line 345
def subst_tb (Z : Var) (P : typ) (b : bind) : bind :=
  match b with
  | bind.bind_sub T => bind.bind_sub (subst_tt Z P T)
  | bind.bind_typ T => bind.bind_typ (subst_tt Z P T)

-- Map a type substitution over an environment
def map_subst_tb (Z : Var) (P : typ) (E : env) : env :=
  E.map (fun (p : Var × bind) => (p.1, subst_tb Z P p.2))

-- line 430
theorem open_tt_rec_type_core : ∀ (T : typ) (j : Nat) (V U : typ) (i : Nat), i ≠ j ->
  open_tt_rec j V T = open_tt_rec i U (open_tt_rec j V T) ->
  T = open_tt_rec i U T := by
  intro T j V U i hij hEq
  induction T generalizing i j V U with
  | typ_top =>
      rfl
  | typ_bvar K =>
      -- If the opening index j hits this bvar, then i cannot be K because i ≠ j
      by_cases hj : j = K
      · have hik : i ≠ K := by simpa [hj] using hij
        -- Goal reduces to rfl under i ≠ K
        simp [open_tt_rec, hik]
      · -- Otherwise, the hypothesis directly gives the goal after evaluation
        have : typ.typ_bvar K = open_tt_rec i U (typ.typ_bvar K) := by
          simpa [open_tt_rec, hj] using hEq
        simpa using this
  | typ_fvar X =>
      rfl
  | typ_arrow T1 T2 ih1 ih2 =>
      -- Reduce the hypothesis to component-wise equalities via congrArg, then apply IH
      have h1 : open_tt_rec j V T1 = open_tt_rec i U (open_tt_rec j V T1) := by
        have := congrArg (fun t => match t with
          | typ.typ_arrow a _ => a
          | _ => open_tt_rec j V T1) hEq
        simpa [open_tt_rec] using this
      have h2 : open_tt_rec j V T2 = open_tt_rec i U (open_tt_rec j V T2) := by
        have := congrArg (fun t => match t with
          | typ.typ_arrow _ b => b
          | _ => open_tt_rec j V T2) hEq
        simpa [open_tt_rec] using this
      have ih1' := ih1 j V U i hij h1
      have ih2' := ih2 j V U i hij h2
      change typ.typ_arrow T1 T2 = typ.typ_arrow (open_tt_rec i U T1) (open_tt_rec i U T2)
      simp [ih1'.symm, ih2'.symm]
  | typ_all T1 T2 ih1 ih2 =>
      -- Similar to arrow, with shifted indices in the body
      have h1 : open_tt_rec j V T1 = open_tt_rec i U (open_tt_rec j V T1) := by
        have := congrArg (fun t => match t with
          | typ.typ_all a _ => a
          | _ => open_tt_rec j V T1) hEq
        simpa [open_tt_rec] using this
      have h2 : open_tt_rec (j + 1) V T2 = open_tt_rec (i + 1) U (open_tt_rec (j + 1) V T2) := by
        have := congrArg (fun t => match t with
          | typ.typ_all _ b => b
          | _ => open_tt_rec (j + 1) V T2) hEq
        simpa [open_tt_rec] using this
      have hij' : i + 1 ≠ j + 1 := by
        intro h
        exact hij (Nat.succ.inj h)
      have ih1' := ih1 j V U i hij h1
      have ih2' := ih2 (j + 1) V U (i + 1) hij' h2
      change typ.typ_all T1 T2 = typ.typ_all (open_tt_rec i U T1) (open_tt_rec (i + 1) U T2)
      simp [ih1'.symm, ih2'.symm]

-- line 438
theorem open_tt_rec_type : ∀ (T U : typ),
  def_type T -> ∀ k, T = open_tt_rec k U T := by
  intro T U h
  revert U
  induction h with
  | type_top =>
      intro U k; rfl
  | type_var X =>
      intro U k; rfl
  | type_arrow T1 T2 h1 h2 ih1 ih2 =>
      intro U k
      have hT1 := ih1 U k
      have hT2 := ih2 U k
      have s1 := congrArg (fun x => typ.typ_arrow x T2) hT1
      have s2 := congrArg (fun y => typ.typ_arrow (open_tt_rec k U T1) y) hT2
      exact s1.trans s2
  | type_all L T1 T2 h1 hBody ih1 ihBody =>
      intro U k
      have hT1 := ih1 U k
      -- Pick a fresh variable X ∉ L.
      classical
      obtain ⟨X, hXfresh⟩ := var_fresh L
      -- From the induction hypothesis on the body instantiated at X, we have
      -- (T2 open_tt_var X) = open_tt_rec (k+1) U (T2 open_tt_var X).
      have hOpened : (T2 open_tt_var X) = open_tt_rec (k + 1) U (T2 open_tt_var X) := by
        exact ihBody X hXfresh U (k + 1)
      -- Rewrite this equality to the shape expected by the core lemma.
      have hCorePrem : open_tt_rec 0 (typ.typ_fvar X) T2 =
                       open_tt_rec (k + 1) U (open_tt_rec 0 (typ.typ_fvar X) T2) := by
        simpa [open_tt, open_tt_rec] using hOpened
      -- Since (k + 1) ≠ 0, we can appeal to the core lemma to conclude on T2.
      have hNe : (k + 1) ≠ 0 := Nat.succ_ne_zero k
      have hT2 : T2 = open_tt_rec (k + 1) U T2 :=
        open_tt_rec_type_core T2 0 (typ.typ_fvar X) U (k + 1) hNe hCorePrem
      -- Finally, assemble the result for the whole forall type.
      have s1 := congrArg (fun x => typ.typ_all x T2) hT1
      have s2 := congrArg (fun y => typ.typ_all (open_tt_rec k U T1) y) hT2
      exact s1.trans s2

-- line 447
theorem subst_tt_fresh : ∀ (Z : Var) (U T : typ),
  Z ∉ fv_tt T -> subst_tt Z U T = T := by
  intro Z U T
  induction T with
  | typ_top =>
      intro; simp [subst_tt]
  | typ_bvar J =>
      intro; simp [subst_tt]
  | typ_fvar X =>
      intro H
      classical
      by_cases h : X = Z
      · have : Z ∈ ({X} : Vars) := by simp [Finset.mem_singleton, h.symm]
        exact (False.elim (H this))
      · simp [subst_tt, h]
  | typ_arrow T1 T2 ih1 ih2 =>
      intro H
      have h1 : Z ∉ fv_tt T1 := by
        intro hz
        have : Z ∈ fv_tt T1 ∪ fv_tt T2 := by exact Finset.mem_union.mpr (Or.inl hz)
        exact H this
      have h2 : Z ∉ fv_tt T2 := by
        intro hz
        have : Z ∈ fv_tt T1 ∪ fv_tt T2 := by exact Finset.mem_union.mpr (Or.inr hz)
        exact H this
      simp [subst_tt, ih1 h1, ih2 h2]
  | typ_all T1 T2 ih1 ih2 =>
      intro H
      have h1 : Z ∉ fv_tt T1 := by
        intro hz
        have : Z ∈ fv_tt T1 ∪ fv_tt T2 := by exact Finset.mem_union.mpr (Or.inl hz)
        exact H this
      have h2 : Z ∉ fv_tt T2 := by
        intro hz
        have : Z ∈ fv_tt T1 ∪ fv_tt T2 := by exact Finset.mem_union.mpr (Or.inr hz)
        exact H this
      simp [subst_tt, ih1 h1, ih2 h2]

-- line 456
theorem subst_tt_open_tt_rec : ∀ (T1 T2 : typ) (Z : Var) (P : typ) (n : Nat), def_type P ->
  subst_tt Z P (open_tt_rec n T2 T1) =
  open_tt_rec n (subst_tt Z P T2) (subst_tt Z P T1) := by
  intro T1 T2 Z P n hP
  revert n Z
  induction T1 with
  | typ_top =>
      intro Z n; simp [open_tt_rec, subst_tt]
  | typ_bvar J =>
      intro Z n
      by_cases h : n = J
      · simp [open_tt_rec, subst_tt, h]
      · simp [open_tt_rec, subst_tt, h]
  | typ_fvar Y =>
      intro Z n
      classical
      by_cases hYZ : Y = Z
      · -- When Y = Z, substitution replaces the variable by P on the left.
        -- On the right, opening a locally closed type P is a no-op.
        subst hYZ
        have : open_tt_rec n (subst_tt Y P T2) P = P := by
          have := open_tt_rec_type P (subst_tt Y P T2) hP n
          simpa using this.symm
        simp [open_tt_rec, subst_tt, this]
      · -- When Y ≠ Z, substitution does nothing and opening a free var is a no-op.
        simp [open_tt_rec, subst_tt, hYZ]
  | typ_arrow T1 T2 ih1 ih2 =>
      intro Z n; simp [open_tt_rec, subst_tt, ih1, ih2]
  | typ_all T1 T2 ih1 ih2 =>
      intro Z n; simp [open_tt_rec, subst_tt, ih1, ih2]
theorem subst_tt_open_tt : ∀ (T1 T2 : typ) (X : Var) (P : typ), def_type P ->
  subst_tt X P (open_tt T1 T2) =
  open_tt (subst_tt X P T1) (subst_tt X P T2) := by
  intro T1 T2 X P hP
  simpa [open_tt] using (subst_tt_open_tt_rec T1 T2 X P 0 hP)

-- line 476
theorem subst_tt_open_tt_var : ∀ (X Y : Var) (U T : typ), Y ≠ X -> def_type U ->
  open_tt (subst_tt X U T) (typ.typ_fvar Y) = subst_tt X U (open_tt T (typ.typ_fvar Y)) := by
  intro X Y U T hYX hU
  classical
  have h := subst_tt_open_tt T (typ.typ_fvar Y) X U hU
  simpa [subst_tt, hYX] using h.symm

-- line 486
theorem subst_tt_intro : ∀ (X : Var) (T2 U : typ),
  X ∉ fv_tt T2 -> def_type U ->
  open_tt T2 U = subst_tt X U (open_tt T2 (typ.typ_fvar X)) := by
  intro X T2 U hFresh hType
  have h1 : subst_tt X U T2 = T2 := subst_tt_fresh X U T2 hFresh
  have h2 : subst_tt X U (typ.typ_fvar X) = U := by
    classical
    simp [subst_tt]
  have H := subst_tt_open_tt T2 (typ.typ_fvar X) X U hType
  calc
    open_tt T2 U = open_tt (subst_tt X U T2) (subst_tt X U (typ.typ_fvar X)) := by simp [h1, h2]
    _ = subst_tt X U (open_tt T2 (typ.typ_fvar X)) := by exact H.symm

-- line 498
theorem open_te_rec_term_core : ∀ (e : trm) (j : Nat) (u : trm) (i : Nat) (P : typ),
  open_ee_rec j u e = open_te_rec i P (open_ee_rec j u e) ->
  e = open_te_rec i P e := by
  intro e j u i P hEq
  induction e generalizing j i with
  | trm_bvar k =>
      simp [open_te_rec]
  | trm_fvar x =>
      simp [open_te_rec]
  | trm_abs V e1 ih =>
      have hV : V = open_tt_rec i P V := by
        have hv := congrArg (fun t => match t with
          | trm.trm_abs V' _ => V'
          | _ => V) hEq
        simpa [open_ee_rec, open_te_rec] using hv
      have hBody : open_ee_rec (j + 1) u e1 = open_te_rec i P (open_ee_rec (j + 1) u e1) := by
        have hb := congrArg (fun t => match t with
          | trm.trm_abs _ e' => e'
          | _ => open_ee_rec (j + 1) u e1) hEq
        simpa [open_ee_rec, open_te_rec] using hb
      have ih' := ih (j + 1) i hBody
      -- rewrite LHS components, then fold back with definitional equality of open_te_rec
      have hb : open_te_rec i P (trm.trm_abs V e1) = trm.trm_abs (open_tt_rec i P V) (open_te_rec i P e1) := rfl
      have hAbs : trm.trm_abs V e1 = trm.trm_abs (open_tt_rec i P V) (open_te_rec i P e1) := by
        have hv2 := congrArg (fun V0 => trm.trm_abs V0 e1) hV
        have he2 := congrArg (fun e0 => trm.trm_abs (open_tt_rec i P V) e0) ih'
        exact hv2.trans he2
      exact hAbs.trans hb.symm
  | trm_app e1 e2 ih1 ih2 =>
      have h1 : open_ee_rec j u e1 = open_te_rec i P (open_ee_rec j u e1) := by
        have h := congrArg (fun t => match t with
          | trm.trm_app a _ => a
          | _ => open_ee_rec j u e1) hEq
        simpa [open_ee_rec, open_te_rec] using h
      have h2 : open_ee_rec j u e2 = open_te_rec i P (open_ee_rec j u e2) := by
        have h := congrArg (fun t => match t with
          | trm.trm_app _ b => b
          | _ => open_ee_rec j u e2) hEq
        simpa [open_ee_rec, open_te_rec] using h
      have ih1' := ih1 j i h1
      have ih2' := ih2 j i h2
      have hb : open_te_rec i P (trm.trm_app e1 e2) = trm.trm_app (open_te_rec i P e1) (open_te_rec i P e2) := rfl
      have hApp : trm.trm_app e1 e2 = trm.trm_app (open_te_rec i P e1) (open_te_rec i P e2) := by
        have he1 := congrArg (fun e0 => trm.trm_app e0 e2) ih1'
        have he2 := congrArg (fun e0 => trm.trm_app (open_te_rec i P e1) e0) ih2'
        exact he1.trans he2
      exact hApp.trans hb.symm
  | trm_tabs V e1 ih =>
      have hV : V = open_tt_rec i P V := by
        have hv := congrArg (fun t => match t with
          | trm.trm_tabs V' _ => V'
          | _ => V) hEq
        simpa [open_ee_rec, open_te_rec] using hv
      have hBody : open_ee_rec j u e1 = open_te_rec (i + 1) P (open_ee_rec j u e1) := by
        have hb := congrArg (fun t => match t with
          | trm.trm_tabs _ e' => e'
          | _ => open_ee_rec j u e1) hEq
        simpa [open_ee_rec, open_te_rec] using hb
      have ih' := ih j (i + 1) hBody
      have hb : open_te_rec i P (trm.trm_tabs V e1) = trm.trm_tabs (open_tt_rec i P V) (open_te_rec (i + 1) P e1) := rfl
      have hTabs : trm.trm_tabs V e1 = trm.trm_tabs (open_tt_rec i P V) (open_te_rec (i + 1) P e1) := by
        have hv2 := congrArg (fun V0 => trm.trm_tabs V0 e1) hV
        have he2 := congrArg (fun e0 => trm.trm_tabs (open_tt_rec i P V) e0) ih'
        exact hv2.trans he2
      exact hTabs.trans hb.symm
  | trm_tapp e1 V ih =>
      have h1 : open_ee_rec j u e1 = open_te_rec i P (open_ee_rec j u e1) := by
        have h := congrArg (fun t => match t with
          | trm.trm_tapp a _ => a
          | _ => open_ee_rec j u e1) hEq
        simpa [open_ee_rec, open_te_rec] using h
      have ih' := ih j i h1
      have hV : V = open_tt_rec i P V := by
        have hv := congrArg (fun t => match t with
          | trm.trm_tapp _ V' => V'
          | _ => V) hEq
        simpa [open_ee_rec, open_te_rec] using hv
      have hb : open_te_rec i P (trm.trm_tapp e1 V) = trm.trm_tapp (open_te_rec i P e1) (open_tt_rec i P V) := rfl
      have hTapp : trm.trm_tapp e1 V = trm.trm_tapp (open_te_rec i P e1) (open_tt_rec i P V) := by
        have he2 := congrArg (fun e0 => trm.trm_tapp e0 V) ih'
        have hv2 := congrArg (fun V0 => trm.trm_tapp (open_te_rec i P e1) V0) hV
        exact he2.trans hv2
      exact hTapp.trans hb.symm

-- line 505
theorem open_te_rec_type_core : ∀ (e : trm) (j : Nat) (Q : typ) (i : Nat) (P : typ), i ≠ j ->
  open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) ->
  e = open_te_rec i P e := by
  intro e j Q i P hij hEq
  induction e generalizing j i with
  | trm_bvar k =>
      simp [open_te_rec]
  | trm_fvar x =>
      simp [open_te_rec]
  | trm_abs V e1 ih =>
      have hV' : open_tt_rec j Q V = open_tt_rec i P (open_tt_rec j Q V) := by
        have h := congrArg (fun t => match t with
          | trm.trm_abs V' _ => V'
          | _ => open_tt_rec j Q V) hEq
        simpa [open_te_rec] using h
      have hE1' : open_te_rec j Q e1 = open_te_rec i P (open_te_rec j Q e1) := by
        have h := congrArg (fun t => match t with
          | trm.trm_abs _ e' => e'
          | _ => open_te_rec j Q e1) hEq
        simpa [open_te_rec] using h
      have hV : V = open_tt_rec i P V :=
        open_tt_rec_type_core V j Q P i hij hV'
      have ih' := ih j i hij hE1'
      have hb : open_te_rec i P (trm.trm_abs V e1) = trm.trm_abs (open_tt_rec i P V) (open_te_rec i P e1) := rfl
      have hAbs : trm.trm_abs V e1 = trm.trm_abs (open_tt_rec i P V) (open_te_rec i P e1) := by
        have hv2 := congrArg (fun V0 => trm.trm_abs V0 e1) hV
        have he2 := congrArg (fun e0 => trm.trm_abs (open_tt_rec i P V) e0) ih'
        exact hv2.trans he2
      exact hAbs.trans hb.symm
  | trm_app e1 e2 ih1 ih2 =>
      have h1 : open_te_rec j Q e1 = open_te_rec i P (open_te_rec j Q e1) := by
        have h := congrArg (fun t => match t with
          | trm.trm_app a _ => a
          | _ => open_te_rec j Q e1) hEq
        simpa [open_te_rec] using h
      have h2 : open_te_rec j Q e2 = open_te_rec i P (open_te_rec j Q e2) := by
        have h := congrArg (fun t => match t with
          | trm.trm_app _ b => b
          | _ => open_te_rec j Q e2) hEq
        simpa [open_te_rec] using h
      have ih1' := ih1 j i hij h1
      have ih2' := ih2 j i hij h2
      have hb : open_te_rec i P (trm.trm_app e1 e2) = trm.trm_app (open_te_rec i P e1) (open_te_rec i P e2) := rfl
      have hApp : trm.trm_app e1 e2 = trm.trm_app (open_te_rec i P e1) (open_te_rec i P e2) := by
        have he1 := congrArg (fun e0 => trm.trm_app e0 e2) ih1'
        have he2 := congrArg (fun e0 => trm.trm_app (open_te_rec i P e1) e0) ih2'
        exact he1.trans he2
      exact hApp.trans hb.symm
  | trm_tabs V e1 ih =>
      have hV' : open_tt_rec j Q V = open_tt_rec i P (open_tt_rec j Q V) := by
        have h := congrArg (fun t => match t with
          | trm.trm_tabs V' _ => V'
          | _ => open_tt_rec j Q V) hEq
        simpa [open_te_rec] using h
      have hE1' : open_te_rec (j + 1) Q e1 = open_te_rec (i + 1) P (open_te_rec (j + 1) Q e1) := by
        have h := congrArg (fun t => match t with
          | trm.trm_tabs _ e' => e'
          | _ => open_te_rec (j + 1) Q e1) hEq
        simpa [open_te_rec] using h
      have hij' : i + 1 ≠ j + 1 := by
        intro h; exact hij (Nat.succ.inj h)
      have hV : V = open_tt_rec i P V := open_tt_rec_type_core V j Q P i hij hV'
      have ih' := ih (j + 1) (i + 1) hij' hE1'
      have hb : open_te_rec i P (trm.trm_tabs V e1) = trm.trm_tabs (open_tt_rec i P V) (open_te_rec (i + 1) P e1) := rfl
      have hTabs : trm.trm_tabs V e1 = trm.trm_tabs (open_tt_rec i P V) (open_te_rec (i + 1) P e1) := by
        have hv2 := congrArg (fun V0 => trm.trm_tabs V0 e1) hV
        have he2 := congrArg (fun e0 => trm.trm_tabs (open_tt_rec i P V) e0) ih'
        exact hv2.trans he2
      exact hTabs.trans hb.symm
  | trm_tapp e1 V ih =>
      have h1 : open_te_rec j Q e1 = open_te_rec i P (open_te_rec j Q e1) := by
        have h := congrArg (fun t => match t with
          | trm.trm_tapp a _ => a
          | _ => open_te_rec j Q e1) hEq
        simpa [open_te_rec] using h
      have hV' : open_tt_rec j Q V = open_tt_rec i P (open_tt_rec j Q V) := by
        have h := congrArg (fun t => match t with
          | trm.trm_tapp _ V' => V'
          | _ => open_tt_rec j Q V) hEq
        simpa [open_te_rec] using h
      have ih' := ih j i hij h1
      have hV : V = open_tt_rec i P V :=
        open_tt_rec_type_core V j Q P i hij hV'
      have hb : open_te_rec i P (trm.trm_tapp e1 V) = trm.trm_tapp (open_te_rec i P e1) (open_tt_rec i P V) := rfl
      have hTapp : trm.trm_tapp e1 V = trm.trm_tapp (open_te_rec i P e1) (open_tt_rec i P V) := by
        have he2 := congrArg (fun e0 => trm.trm_tapp e0 V) ih'
        have hv2 := congrArg (fun V0 => trm.trm_tapp (open_te_rec i P e1) V0) hV
        exact he2.trans hv2
      exact hTapp.trans hb.symm

-- line 514
theorem open_te_rec_term : ∀ (e : trm) (U : typ),
  def_term e -> ∀ k, e = open_te_rec k U e := by
  intro e U h
  revert U
  induction h with
  | term_var x =>
      intro U k; simp [open_te_rec]
  | term_abs L V e1 hVT hBody ih =>
      intro U k
      have hV := open_tt_rec_type V U hVT k
      classical
      obtain ⟨x, hx⟩ := var_fresh L
      have ihBody := ih x hx U k
      have hCore : open_ee_rec 0 (trm.trm_fvar x) e1 = open_te_rec k U (open_ee_rec 0 (trm.trm_fvar x) e1) := by
        simpa [open_ee, open_te] using ihBody
      have hE1 : e1 = open_te_rec k U e1 :=
        open_te_rec_term_core e1 0 (trm.trm_fvar x) k U hCore
      have hb : open_te_rec k U (trm.trm_abs V e1) = trm.trm_abs (open_tt_rec k U V) (open_te_rec k U e1) := rfl
      have hAbs : trm.trm_abs V e1 = trm.trm_abs (open_tt_rec k U V) (open_te_rec k U e1) := by
        have hv2 := congrArg (fun V0 => trm.trm_abs V0 e1) hV
        have he2 := congrArg (fun e0 => trm.trm_abs (open_tt_rec k U V) e0) hE1
        exact hv2.trans he2
      exact hAbs.trans hb.symm
  | term_app e1 e2 h1 h2 ih1 ih2 =>
      intro U k
      have ih1' := ih1 U k
      have ih2' := ih2 U k
      have hb : open_te_rec k U (trm.trm_app e1 e2) = trm.trm_app (open_te_rec k U e1) (open_te_rec k U e2) := rfl
      have hApp : trm.trm_app e1 e2 = trm.trm_app (open_te_rec k U e1) (open_te_rec k U e2) := by
        have he1 := congrArg (fun e0 => trm.trm_app e0 e2) ih1'
        have he2 := congrArg (fun e0 => trm.trm_app (open_te_rec k U e1) e0) ih2'
        exact he1.trans he2
      exact hApp.trans hb.symm
  | term_tabs L V e1 hVT hBody ih =>
      intro U k
      have hV := open_tt_rec_type V U hVT k
      classical
      obtain ⟨X, hX⟩ := var_fresh L
      have ihBody' := ih X hX U (k + 1)
      have hCore : open_te_rec 0 (typ.typ_fvar X) e1 = open_te_rec (k + 1) U (open_te_rec 0 (typ.typ_fvar X) e1) := by
        simpa [open_te] using ihBody'
      have hNe : (k + 1) ≠ 0 := Nat.succ_ne_zero k
      have hE1 : e1 = open_te_rec (k + 1) U e1 :=
        open_te_rec_type_core e1 0 (typ.typ_fvar X) (k + 1) U hNe hCore
      have hb : open_te_rec k U (trm.trm_tabs V e1) = trm.trm_tabs (open_tt_rec k U V) (open_te_rec (k + 1) U e1) := rfl
      have hTabs : trm.trm_tabs V e1 = trm.trm_tabs (open_tt_rec k U V) (open_te_rec (k + 1) U e1) := by
        have hv2 := congrArg (fun V0 => trm.trm_tabs V0 e1) hV
        have he2 := congrArg (fun e0 => trm.trm_tabs (open_tt_rec k U V) e0) hE1
        exact hv2.trans he2
      exact hTabs.trans hb.symm
  | term_tapp e1 V hE hT ih =>
      intro U k
      have ih' := ih U k
      have hV := open_tt_rec_type V U hT k
      have hb : open_te_rec k U (trm.trm_tapp e1 V) = trm.trm_tapp (open_te_rec k U e1) (open_tt_rec k U V) := rfl
      have hTapp : trm.trm_tapp e1 V = trm.trm_tapp (open_te_rec k U e1) (open_tt_rec k U V) := by
        have he2 := congrArg (fun e0 => trm.trm_tapp e0 V) ih'
        have hv2 := congrArg (fun V0 => trm.trm_tapp (open_te_rec k U e1) V0) hV
        exact he2.trans hv2
      exact hTapp.trans hb.symm

-- line 526
theorem subst_te_fresh : ∀ (X : Var) (U : typ) (e : trm),
  X ∉ fv_te e -> subst_te X U e = e := by
  intro X U e
  induction e with
  | trm_bvar i => intro; simp [subst_te]
  | trm_fvar x => intro; simp [subst_te]
  | trm_abs V e1 ih =>
      intro H
      have hV : X ∉ fv_tt V := by
        intro hz
        have : X ∈ fv_tt V ∪ fv_te e1 := by exact Finset.mem_union.mpr (Or.inl hz)
        exact H this
      have hE : X ∉ fv_te e1 := by
        intro hz
        have : X ∈ fv_tt V ∪ fv_te e1 := by exact Finset.mem_union.mpr (Or.inr hz)
        exact H this
      simp [subst_te, subst_tt_fresh, ih hE, hV]
  | trm_app e1 e2 ih1 ih2 =>
      intro H
      have h1 : X ∉ fv_te e1 := by
        intro hz; exact H (Finset.mem_union.mpr (Or.inl hz))
      have h2 : X ∉ fv_te e2 := by
        intro hz; exact H (Finset.mem_union.mpr (Or.inr hz))
      simp [subst_te, ih1 h1, ih2 h2]
  | trm_tabs V e1 ih =>
    intro H
    have hV : X ∉ fv_tt V := by
      intro hz; exact H (Finset.mem_union.mpr (Or.inl hz))
    have hE : X ∉ fv_te e1 := by
      intro hz; exact H (Finset.mem_union.mpr (Or.inr hz))
    simp [subst_te, subst_tt_fresh, ih hE, hV]
  | trm_tapp e1 V ih =>
    intro H
    have hV : X ∉ fv_tt V := by
      intro hz; exact H (Finset.mem_union.mpr (Or.inl hz))
    have hE : X ∉ fv_te e1 := by
      intro hz; exact H (Finset.mem_union.mpr (Or.inr hz))
    simp [subst_te, subst_tt_fresh, ih hE, hV]

-- line 535
theorem subst_te_open_te : ∀ (e : trm) (T : typ) (X : Var) (U : typ), def_type U ->
  subst_te X U (open_te e T) =
  open_te (subst_te X U e) (subst_tt X U T) := by
  intro e T X U hType
  -- Generalize over the opening index
  have gen : ∀ (n : Nat) (e : trm) (T : typ),
      subst_te X U (open_te_rec n T e) =
      open_te_rec n (subst_tt X U T) (subst_te X U e) := by
    intro n e
    induction e generalizing n with
    | trm_bvar i =>
        intro T; simp [open_te_rec, subst_te]
    | trm_fvar x =>
        intro T; simp [open_te_rec, subst_te]
    | trm_abs V e1 ih =>
        intro T; simp [open_te_rec, subst_te, subst_tt_open_tt_rec, hType, ih]
    | trm_app e1 e2 ih1 ih2 =>
        intro T; simp [open_te_rec, subst_te, ih1, ih2]
    | trm_tabs V e1 ih =>
        intro T; simp [open_te_rec, subst_te, subst_tt_open_tt_rec, hType, ih (n + 1)]
    | trm_tapp e1 V ih =>
        intro T; simp [open_te_rec, subst_te, subst_tt_open_tt_rec, hType, ih]
  simpa [open_te] using gen 0 e T

-- line 546
theorem subst_te_open_te_var : ∀ (X Y : Var) (U : typ) (e : trm), Y ≠ X -> def_type U ->
  open_te (subst_te X U e) (typ.typ_fvar Y) = subst_te X U (open_te e (typ.typ_fvar Y)) := by
  intro X Y U e hYX hU
  classical
  have h := subst_te_open_te e (typ.typ_fvar Y) X U hU
  simpa [subst_tt, hYX] using h.symm

-- line 556
theorem subst_te_intro : ∀ (X : Var) (U : typ) (e : trm),
  X ∉ fv_te e -> def_type U ->
  open_te e U = subst_te X U (open_te e (typ.typ_fvar X)) := by
  intro X U e hFresh hU
  have hf := subst_te_fresh X U e hFresh
  have hsubstVar : subst_tt X U (typ.typ_fvar X) = U := by
    classical
    simp [subst_tt]
  have H := subst_te_open_te e (typ.typ_fvar X) X U hU
  -- H: subst_te X U (open_te e (typ.typ_fvar X)) = open_te (subst_te X U e) (subst_tt X U (typ.typ_fvar X))
  -- rewrite RHS using hsubstVar, then rewrite e using hf
  have H' : subst_te X U (open_te e (typ.typ_fvar X)) = open_te (subst_te X U e) U := by
    simpa [hsubstVar] using H
  -- we want open_te e U = LHS; from hf, open_te e U = open_te (subst_te X U e) U
  have : open_te e U = open_te (subst_te X U e) U := by simp [hf]
  exact this.trans H'.symm

-- line 568
theorem open_ee_rec_term_core : ∀ (e : trm) (j : Nat) (v u : trm) (i : Nat), i ≠ j ->
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) ->
  e = open_ee_rec i u e := by
  intro e j v u i hij hEq
  induction e generalizing j i with
  | trm_bvar k =>
      by_cases hj : j = k
      · have hik : i ≠ k := by simpa [hj] using hij
        simp [open_ee_rec, hik]
      · have : trm.trm_bvar k = open_ee_rec i u (trm.trm_bvar k) := by
          simpa [open_ee_rec, hj] using hEq
        exact this
  | trm_fvar x =>
      simp [open_ee_rec]
  | trm_abs V e1 ih =>
      have hBody : open_ee_rec (j + 1) v e1 = open_ee_rec (i + 1) u (open_ee_rec (j + 1) v e1) := by
        have h := congrArg (fun t => match t with
          | trm.trm_abs _ e' => e'
          | _ => open_ee_rec (j + 1) v e1) hEq
        simpa [open_ee_rec] using h
      have hij' : i + 1 ≠ j + 1 := by
        intro h; exact hij (Nat.succ.inj h)
      have ih' := ih (j + 1) (i + 1) hij' hBody
      have hb : open_ee_rec i u (trm.trm_abs V e1) = trm.trm_abs V (open_ee_rec (i + 1) u e1) := rfl
      have hAbs : trm.trm_abs V e1 = trm.trm_abs V (open_ee_rec (i + 1) u e1) := by
        exact congrArg (fun e0 => trm.trm_abs V e0) ih'
      exact hAbs.trans hb.symm
  | trm_app e1 e2 ih1 ih2 =>
      have h1 : open_ee_rec j v e1 = open_ee_rec i u (open_ee_rec j v e1) := by
        have h := congrArg (fun t => match t with
          | trm.trm_app a _ => a
          | _ => open_ee_rec j v e1) hEq
        simpa [open_ee_rec] using h
      have h2 : open_ee_rec j v e2 = open_ee_rec i u (open_ee_rec j v e2) := by
        have h := congrArg (fun t => match t with
          | trm.trm_app _ b => b
          | _ => open_ee_rec j v e2) hEq
        simpa [open_ee_rec] using h
      have ih1' := ih1 j i hij h1
      have ih2' := ih2 j i hij h2
      have hb : open_ee_rec i u (trm.trm_app e1 e2) = trm.trm_app (open_ee_rec i u e1) (open_ee_rec i u e2) := rfl
      have hApp : trm.trm_app e1 e2 = trm.trm_app (open_ee_rec i u e1) (open_ee_rec i u e2) := by
        have he1 := congrArg (fun e0 => trm.trm_app e0 e2) ih1'
        have he2 := congrArg (fun e0 => trm.trm_app (open_ee_rec i u e1) e0) ih2'
        exact he1.trans he2
      exact hApp.trans hb.symm
  | trm_tabs V e1 ih =>
      have hBody : open_ee_rec j v e1 = open_ee_rec i u (open_ee_rec j v e1) := by
        have h := congrArg (fun t => match t with
          | trm.trm_tabs _ e' => e'
          | _ => open_ee_rec j v e1) hEq
        simpa [open_ee_rec] using h
      have ih' := ih j i hij hBody
      have hb : open_ee_rec i u (trm.trm_tabs V e1) = trm.trm_tabs V (open_ee_rec i u e1) := rfl
      have hTabs : trm.trm_tabs V e1 = trm.trm_tabs V (open_ee_rec i u e1) := by
        exact congrArg (fun e0 => trm.trm_tabs V e0) ih'
      exact hTabs.trans hb.symm
  | trm_tapp e1 V ih =>
      have h1 : open_ee_rec j v e1 = open_ee_rec i u (open_ee_rec j v e1) := by
        have h := congrArg (fun t => match t with
          | trm.trm_tapp a _ => a
          | _ => open_ee_rec j v e1) hEq
        simpa [open_ee_rec] using h
      have ih' := ih j i hij h1
      have hb : open_ee_rec i u (trm.trm_tapp e1 V) = trm.trm_tapp (open_ee_rec i u e1) V := rfl
      have hTapp : trm.trm_tapp e1 V = trm.trm_tapp (open_ee_rec i u e1) V := by
        exact congrArg (fun e0 => trm.trm_tapp e0 V) ih'
      exact hTapp.trans hb.symm

-- line 576
theorem open_ee_rec_type_core : ∀ (e : trm) (j : Nat) (V : typ) (u : trm) (i : Nat),
  open_te_rec j V e = open_ee_rec i u (open_te_rec j V e) ->
  e = open_ee_rec i u e := by
  intro e j V u i hEq
  induction e generalizing j i with
  | trm_bvar k =>
      simpa [open_te_rec] using hEq
  | trm_fvar x =>
      simpa [open_te_rec] using hEq
  | trm_abs V0 e1 ih =>
      have hE1 : open_te_rec j V e1 = open_ee_rec (i + 1) u (open_te_rec j V e1) := by
        have h := congrArg (fun t => match t with
          | trm.trm_abs _ e' => e'
          | _ => open_te_rec j V e1) hEq
        simpa [open_te_rec, open_ee_rec] using h
      have ih' := ih j (i + 1) hE1
      have hb : open_ee_rec i u (trm.trm_abs V0 e1) = trm.trm_abs V0 (open_ee_rec (i + 1) u e1) := rfl
      have hAbs : trm.trm_abs V0 e1 = trm.trm_abs V0 (open_ee_rec (i + 1) u e1) := by
        exact congrArg (fun e0 => trm.trm_abs V0 e0) ih'
      exact hAbs.trans hb.symm
  | trm_app e1 e2 ih1 ih2 =>
      have h1 : open_te_rec j V e1 = open_ee_rec i u (open_te_rec j V e1) := by
        have h := congrArg (fun t => match t with
          | trm.trm_app a _ => a
          | _ => open_te_rec j V e1) hEq
        simpa [open_te_rec, open_ee_rec] using h
      have h2 : open_te_rec j V e2 = open_ee_rec i u (open_te_rec j V e2) := by
        have h := congrArg (fun t => match t with
          | trm.trm_app _ b => b
          | _ => open_te_rec j V e2) hEq
        simpa [open_te_rec, open_ee_rec] using h
      have ih1' := ih1 j i h1
      have ih2' := ih2 j i h2
      have hb : open_ee_rec i u (trm.trm_app e1 e2) = trm.trm_app (open_ee_rec i u e1) (open_ee_rec i u e2) := rfl
      have hApp : trm.trm_app e1 e2 = trm.trm_app (open_ee_rec i u e1) (open_ee_rec i u e2) := by
        have he1 := congrArg (fun e0 => trm.trm_app e0 e2) ih1'
        have he2 := congrArg (fun e0 => trm.trm_app (open_ee_rec i u e1) e0) ih2'
        exact he1.trans he2
      exact hApp.trans hb.symm
  | trm_tabs V0 e1 ih =>
      have hE1 : open_te_rec (j + 1) V e1 = open_ee_rec i u (open_te_rec (j + 1) V e1) := by
        have h := congrArg (fun t => match t with
          | trm.trm_tabs _ e' => e'
          | _ => open_te_rec (j + 1) V e1) hEq
        simpa [open_te_rec, open_ee_rec] using h
      have ih' := ih (j + 1) i hE1
      have hb : open_ee_rec i u (trm.trm_tabs V0 e1) = trm.trm_tabs V0 (open_ee_rec i u e1) := rfl
      have hTabs : trm.trm_tabs V0 e1 = trm.trm_tabs V0 (open_ee_rec i u e1) := by
        exact congrArg (fun e0 => trm.trm_tabs V0 e0) ih'
      exact hTabs.trans hb.symm
  | trm_tapp e1 V0 ih =>
      have h1 : open_te_rec j V e1 = open_ee_rec i u (open_te_rec j V e1) := by
        have h := congrArg (fun t => match t with
          | trm.trm_tapp a _ => a
          | _ => open_te_rec j V e1) hEq
        simpa [open_te_rec, open_ee_rec] using h
      have ih' := ih j i h1
      have hb : open_ee_rec i u (trm.trm_tapp e1 V0) = trm.trm_tapp (open_ee_rec i u e1) V0 := rfl
      have hTapp : trm.trm_tapp e1 V0 = trm.trm_tapp (open_ee_rec i u e1) V0 := by
        exact congrArg (fun e0 => trm.trm_tapp e0 V0) ih'
      exact hTapp.trans hb.symm

-- line 583
theorem open_ee_rec_term : ∀ (u e : trm),
  def_term e -> ∀ k, e = open_ee_rec k u e := by
  intro u e h
  revert u
  induction h with
  | term_var x =>
      intro u k; simp [open_ee_rec]
  | term_abs L V e1 hVT hBody ih =>
      intro u k
      classical
      obtain ⟨x, hx⟩ := var_fresh L
      have ihBody := ih x hx u (k + 1)
      have hCore : open_ee_rec 0 (trm.trm_fvar x) e1 = open_ee_rec (k + 1) u (open_ee_rec 0 (trm.trm_fvar x) e1) := by
        simpa [open_ee] using ihBody
      have hNe : (k + 1) ≠ 0 := Nat.succ_ne_zero k
      have hE1 : e1 = open_ee_rec (k + 1) u e1 :=
        open_ee_rec_term_core e1 0 (trm.trm_fvar x) u (k + 1) hNe hCore
      have hb : open_ee_rec k u (trm.trm_abs V e1) = trm.trm_abs V (open_ee_rec (k + 1) u e1) := rfl
      have hAbs : trm.trm_abs V e1 = trm.trm_abs V (open_ee_rec (k + 1) u e1) := by
        exact congrArg (fun e0 => trm.trm_abs V e0) hE1
      exact hAbs.trans hb.symm
  | term_app e1 e2 h1 h2 ih1 ih2 =>
      intro u k
      have ih1' := ih1 u k
      have ih2' := ih2 u k
      have hb : open_ee_rec k u (trm.trm_app e1 e2) = trm.trm_app (open_ee_rec k u e1) (open_ee_rec k u e2) := rfl
      have hApp : trm.trm_app e1 e2 = trm.trm_app (open_ee_rec k u e1) (open_ee_rec k u e2) := by
        have he1 := congrArg (fun e0 => trm.trm_app e0 e2) ih1'
        have he2 := congrArg (fun e0 => trm.trm_app (open_ee_rec k u e1) e0) ih2'
        exact he1.trans he2
      exact hApp.trans hb.symm
  | term_tabs L V e1 hVT hBody ih =>
      intro u k
      classical
      obtain ⟨X, hX⟩ := var_fresh L
      have ihBody' := ih X hX u k
      have hCore : open_te_rec 0 (typ.typ_fvar X) e1 = open_ee_rec k u (open_te_rec 0 (typ.typ_fvar X) e1) := by
        simpa [open_te] using ihBody'
      have hE1 : e1 = open_ee_rec k u e1 :=
        open_ee_rec_type_core e1 0 (typ.typ_fvar X) u k hCore
      have hb : open_ee_rec k u (trm.trm_tabs V e1) = trm.trm_tabs V (open_ee_rec k u e1) := rfl
      have hTabs : trm.trm_tabs V e1 = trm.trm_tabs V (open_ee_rec k u e1) := by
        exact congrArg (fun e0 => trm.trm_tabs V e0) hE1
      exact hTabs.trans hb.symm
  | term_tapp e1 V hE hT ih =>
      intro u k
      have ih' := ih u k
      have hb : open_ee_rec k u (trm.trm_tapp e1 V) = trm.trm_tapp (open_ee_rec k u e1) V := rfl
      have hTapp : trm.trm_tapp e1 V = trm.trm_tapp (open_ee_rec k u e1) V := by
        exact congrArg (fun e0 => trm.trm_tapp e0 V) ih'
      exact hTapp.trans hb.symm

-- line 595}
theorem subst_ee_fresh : ∀ (x : Var) (u e : trm),
  x ∉ fv_ee e -> subst_ee x u e = e := by
  intro x u e
  induction e with
  | trm_bvar i => intro; simp [subst_ee]
  | trm_fvar y =>
      intro H
      classical
      by_cases h : y = x
      · have : x ∈ ({y} : Vars) := by simp [Finset.mem_singleton, h.symm]
        exact (False.elim (H this))
      · simp [subst_ee, h]
  | trm_abs V e1 ih =>
      intro H
      have hE : x ∉ fv_ee e1 := by
        intro hz; exact H hz
      simp [subst_ee, ih hE]
  | trm_app e1 e2 ih1 ih2 =>
      intro H
      have h1 : x ∉ fv_ee e1 := by
        intro hz; exact H (Finset.mem_union.mpr (Or.inl hz))
      have h2 : x ∉ fv_ee e2 := by
        intro hz; exact H (Finset.mem_union.mpr (Or.inr hz))
      simp [subst_ee, ih1 h1, ih2 h2]
  | trm_tabs V e1 ih =>
      intro H
      have hE : x ∉ fv_ee e1 := by intro hz; exact H hz
      simp [subst_ee, ih hE]
  | trm_tapp e1 V ih =>
      intro H
      have hE : x ∉ fv_ee e1 := by intro hz; exact H hz
      simp [subst_ee, ih hE]

-- line 604
theorem subst_ee_open_ee : ∀ (t1 t2 u : trm) (x : Var), def_term u ->
  subst_ee x u (open_ee t1 t2) =
  open_ee (subst_ee x u t1) (subst_ee x u t2) := by
  intro t1 t2 u x hU
  -- Generalize over the opening index
  let X := x
  have gen : ∀ (n : Nat) (e : trm),
      subst_ee X u (open_ee_rec n t2 e) =
      open_ee_rec n (subst_ee X u t2) (subst_ee X u e) := by
    intro n e
    induction e generalizing n with
    | trm_bvar i =>
        by_cases hni : n = i
        · simp [open_ee_rec, subst_ee, hni]
        · simp [open_ee_rec, subst_ee, hni]
    | trm_fvar y =>
        classical
        by_cases hyX : y = X
        · have hclose : open_ee_rec n (subst_ee X u t2) u = u := by
            have := open_ee_rec_term (subst_ee X u t2) u hU n
            simpa using this.symm
          simp [open_ee_rec, subst_ee, hyX, hclose]
        · simp [open_ee_rec, subst_ee, hyX]
    | trm_abs V e1 ih =>
        simp [open_ee_rec, subst_ee, ih (n + 1)]
    | trm_app e1 e2 ih1 ih2 =>
        simp [open_ee_rec, subst_ee, ih1 n, ih2 n]
    | trm_tabs V e1 ih =>
        simp [open_ee_rec, subst_ee, ih n]
    | trm_tapp e1 V ih =>
        simp [open_ee_rec, subst_ee, ih n]
  simpa [open_ee] using gen 0 t1


-- line 616
theorem subst_ee_open_ee_var : ∀ (x y : Var) (u e : trm), y ≠ x -> def_term u ->
  open_ee (subst_ee x u e) (trm.trm_fvar y) = subst_ee x u (open_ee e (trm.trm_fvar y)) := by
  intro x y u e hYX hU
  classical
  have h := subst_ee_open_ee e (trm.trm_fvar y) u x hU
  simpa [subst_ee, hYX] using h.symm

-- line 626
theorem subst_ee_intro : ∀ (x : Var) (u e : trm),
  x ∉ fv_ee e -> def_term u ->
  open_ee e u = subst_ee x u (e open_ee_var x) := by
  intro x u e hFresh hU
  have hf := subst_ee_fresh x u e hFresh
  have hvar : subst_ee x u (trm.trm_fvar x) = u := by
    classical
    simp [subst_ee]
  have H := subst_ee_open_ee e (trm.trm_fvar x) u x hU
  -- H: subst_ee x u (open_ee e (trm.trm_fvar x)) = open_ee (subst_ee x u e) (subst_ee x u (trm.trm_fvar x))
  -- rewrite RHS using hvar, then rewrite e using hf
  have H' : subst_ee x u (open_ee e (trm.trm_fvar x)) = open_ee (subst_ee x u e) u := by
    simpa [hvar] using H
  -- we want open_ee e u = LHS; from hf, open_ee e u = open_ee (subst_ee x u e) u
  have : open_ee e u = open_ee (subst_ee x u e) u := by simp [hf]
  exact this.trans H'.symm

-- line 637
theorem subst_te_open_ee_var : ∀ (Z : Var) (P : typ) (x : Var) (e : trm),
  open_ee (subst_te Z P e) (trm.trm_fvar x) = subst_te Z P (open_ee e (trm.trm_fvar x)) := by
  intro Z P x e
  -- Generalize over the opening index and the inserted term
  have gen : ∀ (n : Nat) (e : trm) (t : trm),
      subst_te Z P (open_ee_rec n t e) =
      open_ee_rec n (subst_te Z P t) (subst_te Z P e) := by
    intro n e
    induction e generalizing n with
    | trm_bvar i =>
        intro t
        by_cases h : n = i
        · simp [open_ee_rec, subst_te, h]
        · simp [open_ee_rec, subst_te, h]
    | trm_fvar y =>
        intro t; simp [open_ee_rec, subst_te]
    | trm_abs V e1 ih =>
        intro t; simp [open_ee_rec, subst_te, ih (n + 1)]
    | trm_app e1 e2 ih1 ih2 =>
        intro t; simp [open_ee_rec, subst_te, ih1 n, ih2 n]
    | trm_tabs V e1 ih =>
        intro t; simp [open_ee_rec, subst_te, ih n]
    | trm_tapp e1 V ih =>
        intro t; simp [open_ee_rec, subst_te, ih n]
  -- Use the symmetry of gen to match the goal's direction
  simpa [open_ee] using (gen 0 e (trm.trm_fvar x)).symm

-- line 647
theorem subst_ee_open_te_var : ∀ (z : Var) (u : trm) (e : trm) (X : Var), def_term u ->
  open_te (subst_ee z u e) (typ.typ_fvar X) = subst_ee z u (open_te e (typ.typ_fvar X)) := by
  intro z u e X hU
  -- Prove the generalized commuting property with open_te_rec
  have gen : ∀ (n : Nat) (T : typ) (e : trm),
      subst_ee z u (open_te_rec n T e) =
      open_te_rec n T (subst_ee z u e) := by
    intro n T e
    induction e generalizing n with
    | trm_bvar i =>
        simp [open_te_rec, subst_ee]
    | trm_fvar y =>
        classical
        by_cases hyz : y = z
        · have hclose : open_te_rec n T u = u := by
            have := open_te_rec_term u T hU n
            simpa using this.symm
          simp [open_te_rec, subst_ee, hyz, hclose]
        · simp [open_te_rec, subst_ee, hyz]
    | trm_abs V e1 ih =>
        simp [open_te_rec, subst_ee, ih]
    | trm_app e1 e2 ih1 ih2 =>
        simp [open_te_rec, subst_ee, ih1, ih2]
    | trm_tabs V e1 ih =>
        simp [open_te_rec, subst_ee, ih (n + 1)]
    | trm_tapp e1 V ih =>
        simp [open_te_rec, subst_ee, ih]
  -- Specialize to n = 0 and T = typ_fvar X, then flip the equality direction
  have h := gen 0 (typ.typ_fvar X) e
  simpa [open_te] using h.symm

-- line 657
theorem subst_tt_type : ∀ (T : typ) (Z : Var) (P : typ),
  def_type T -> def_type P -> def_type (subst_tt Z P T) := by
  intro T Z P hT hP
  revert Z P
  induction hT with
  | type_top =>
      intro Z P hP; simp [subst_tt, def_type.type_top]
  | type_var X =>
      intro Z P hP
      classical
      by_cases hXZ : X = Z
      · subst hXZ
        simpa [subst_tt] using hP
      · simp [subst_tt, hXZ, def_type.type_var]
  | type_arrow T1 T2 h1 h2 ih1 ih2 =>
      intro Z P hP
      have h1' := ih1 Z P hP
      have h2' := ih2 Z P hP
      exact def_type.type_arrow (subst_tt Z P T1) (subst_tt Z P T2) h1' h2'
  | type_all L T1 T2 h1 hBody ih1 ihBody =>
      intro Z P hP
      have hT1' := ih1 Z P hP
      refine def_type.type_all (L := L ∪ {Z}) (T1 := subst_tt Z P T1) (T2 := subst_tt Z P T2) hT1' ?_;
      intro X hX
      -- From X ∉ L ∪ {Z}, we have X ∉ L and X ≠ Z
      have hXinL : X ∉ L := by
        intro hxL; exact hX (Finset.mem_union.mpr (Or.inl hxL))
      have hXneZ : X ≠ Z := by
        intro hEq
        have hxIn : X ∈ ({Z} : Vars) := by simp [Finset.mem_singleton, hEq]
        exact hX (Finset.mem_union.mpr (Or.inr hxIn))
      -- Apply IH on the opened body, then rewrite using subst_tt_open_tt_var
      have hBodySub : def_type (subst_tt Z P (T2 open_tt_var X)) := ihBody X hXinL Z P hP
      have hEq := subst_tt_open_tt_var Z X P T2 hXneZ hP
      -- hEq: open_tt (subst_tt Z P T2) (typ.typ_fvar X) = subst_tt Z P (open_tt T2 (typ.typ_fvar X))
      simpa [hEq.symm] using hBodySub

-- line 665
theorem subst_te_term : ∀ (e : trm) (Z : Var) (P : typ),
  def_term e -> def_type P -> def_term (subst_te Z P e) := by
  intro e Z P hE hP
  revert Z P
  induction hE with
  | term_var x =>
      intro Z P hP; simpa [subst_te] using def_term.term_var x
  | term_abs L V e1 hVT hBody ih =>
      intro Z P hP
      have hV' : def_type (subst_tt Z P V) := subst_tt_type V Z P hVT hP
      refine def_term.term_abs (L := L) (V := subst_tt Z P V) (e1 := subst_te Z P e1) hV' ?_;
      intro x hx
      have hx' := ih x hx Z P hP
      -- rewrite opening under type substitution
      simpa [subst_te_open_ee_var] using hx'
  | term_app e1 e2 h1 h2 ih1 ih2 =>
      intro Z P hP
      have h1' := ih1 Z P hP
      have h2' := ih2 Z P hP
      exact def_term.term_app (subst_te Z P e1) (subst_te Z P e2) h1' h2'
  | term_tabs L V e1 hVT hBody ih =>
      intro Z P hP
      have hV' : def_type (subst_tt Z P V) := subst_tt_type V Z P hVT hP
      refine def_term.term_tabs (L := L ∪ {Z}) (V := subst_tt Z P V) (e1 := subst_te Z P e1) hV' ?_;
      intro X hX
      have hXinL : X ∉ L := by
        intro hxL; exact hX (Finset.mem_union.mpr (Or.inl hxL))
      have hBody' := ih X hXinL Z P hP
      have hXneZ : X ≠ Z := by
        intro hEq
        have hxIn : X ∈ ({Z} : Vars) := by simp [Finset.mem_singleton, hEq]
        exact hX (Finset.mem_union.mpr (Or.inr hxIn))
      -- rewrite opening under type substitution
      simpa [subst_te_open_te_var, hXneZ, hP] using hBody'
  | term_tapp e1 V hE1 hT ih =>
      intro Z P hP
      have hE1' := ih Z P hP
      have hV' : def_type (subst_tt Z P V) := subst_tt_type V Z P hT hP
      exact def_term.term_tapp (subst_te Z P e1) (subst_tt Z P V) hE1' hV'

-- line 673
theorem subst_ee_term : ∀ (e1 : trm) (Z : Var) (e2 : trm),
  def_term e1 -> def_term e2 -> def_term (subst_ee Z e2 e1) := by
  intro e1 Z e2 h1 h2
  revert Z e2
  induction h1 with
  | term_var x =>
      intro Z e2 h2
      classical
      by_cases hx : x = Z
      · subst hx; simpa [subst_ee] using h2
      · have : def_term (trm.trm_fvar x) := def_term.term_var x
        simpa [subst_ee, hx] using this
  | term_abs L V e1 hVT hBody ih =>
      intro Z e2 h2
      refine def_term.term_abs (L := L ∪ {Z}) (V := V) (e1 := subst_ee Z e2 e1) hVT ?_;
      intro x hx
      have hXinL : x ∉ L := by
        intro hxL; exact hx (Finset.mem_union.mpr (Or.inl hxL))
      have hxne : x ≠ Z := by
        intro hEq
        have hxIn : x ∈ ({Z} : Vars) := by simp [Finset.mem_singleton, hEq]
        exact hx (Finset.mem_union.mpr (Or.inr hxIn))
      have hBody' := ih x hXinL Z e2 h2
      -- rewrite opening under term substitution
      have hEq := subst_ee_open_ee_var Z x e2 e1 hxne h2
      -- From def_term (subst_ee Z e2 (open_ee e1 (trm.trm_fvar x))) to def_term (open_ee (subst_ee Z e2 e1) (trm.trm_fvar x))
      simpa [hEq.symm] using hBody'
  | term_app e1 e2' hE1 hE2 ih1 ih2 =>
      intro Z e2 h2
      have h1' := ih1 Z e2 h2
      have h2' := ih2 Z e2 h2
      exact def_term.term_app (subst_ee Z e2 e1) (subst_ee Z e2 e2') h1' h2'
  | term_tabs L V e1 hVT hBody ih =>
      intro Z e2 h2
      refine def_term.term_tabs (L := L) (V := V) (e1 := subst_ee Z e2 e1) hVT ?_;
      intro X hX
      have hBody' := ih X hX Z e2 h2
      have hEq := subst_ee_open_te_var Z e2 e1 X h2
      -- From def_term (subst_ee Z e2 (open_te e1 (typ.typ_fvar X))) to def_term (open_te (subst_ee Z e2 e1) (typ.typ_fvar X))
      simpa [hEq] using hBody'
  | term_tapp e1 V hE hT ih =>
    intro Z e2 h2
    have hE' := ih Z e2 h2
    exact def_term.term_tapp (subst_ee Z e2 e1) V hE' hT

-- attributes corresponding to Coq Hints
attribute [aesop safe constructors] def_type def_term wft okt value red
attribute [aesop safe] typing.typing_var typing.typing_app typing.typing_tapp typing.typing_sub
attribute [aesop safe] sub.sub_top sub.sub_refl_tvar sub.sub_arrow

/-
  Properties of well-formedness (wft)
-/

-- line 690
-- Helper lemmas about lookup/binds and empty env
private lemma binds_empty_inv {x : Var} {b : bind} :
  binds x b ([] : env) -> False := by
  intro h
  unfold binds at h
  simp [List.lookup] at h

-- Helper lemmas about lookup/binds under list append
private lemma lookup_append_left {E F : env} {x : Var} {b : bind}
  (h : E.lookup x = some b) : (E ++ F).lookup x = some b := by
  classical
  induction E with
  | nil =>
      -- impossible: [] has no bindings
      cases h
  | cons head tail ih =>
      cases head with
      | mk y bnd =>
        -- Expand lookup on the head, splitting on the boolean test x == y
        have h' : (match x == y with
            | true => some bnd
            | false => tail.lookup x) = some b := by
          simpa [List.lookup] using h
        cases hxy : (x == y) with
        | false =>
          -- lookup skipped the head; reduce to tail then apply IH
          have hTail : tail.lookup x = some b := by
            simpa [hxy] using h'
          have ih' := ih hTail
          -- ((y, bnd) :: tail) ++ F = (y, bnd) :: (tail ++ F)
          simpa [List.lookup, hxy, List.cons_append] using ih'
        | true =>
          -- lookup hit the head; conclude bnd = b and the appended list also hits head
          have hb : bnd = b := by
            -- from h' and hxy, we get some bnd = some b
            simpa [hxy] using h'
          subst hb
          simp [List.lookup, hxy, List.cons_append]

private lemma binds_append_left {E F : env} {x : Var} {b : bind}
  (h : binds x b E) : binds x b (E ++ F) := by
  unfold binds at h ⊢
  exact lookup_append_left (E := E) (F := F) (x := x) (b := b) h

-- A variable cannot be typed from an empty environment
theorem typing_var_empty_absurd {x : Var} {T : typ} :
  typing [] (trm.trm_fvar x) T -> False := by
  intro h
  -- Strong recursion on the typing derivation while constraining E = [] and e = trm_fvar x
  have go : ∀ {E e T}, typing E e T -> (E = [] -> e = trm.trm_fvar x -> False) := by
    intro E e T ht
    induction ht with
    | typing_var E0 x' T' _ hbinds =>
        intro hE he; cases hE; cases he
        have : binds x (bind.bind_typ T') ([] : env) := by simpa using hbinds
        exact binds_empty_inv (x := x) (b := bind.bind_typ T') this
    | typing_abs L E0 V e1 hbody ih =>
        intro hE he; cases he
    | typing_app T1 E0 e1 e2 T2 h1 h2 ih1 ih2 =>
        intro hE he; cases he
    | typing_tabs L E0 V e1 T1 hbody ih =>
        intro hE he; cases he
    | typing_tapp T1 E0 e1 T T2 hAll hSub ih =>
        intro hE he; cases he
    | typing_sub S E0 e0 T0 hS hSub ih =>
        intro hE he; exact ih hE he
  exact go h rfl rfl

-- No subtyping from a forall type to an arrow type
-- Coq Fsub.v lines 1426-1437, 1439-1450 support canonical form proofs via such exclusions
-- Here we prepare shape lemmas specialized to the empty environment.

theorem no_sub_all_to_arrow {E : env} {S1 S2 T1 T2 : typ} :
  sub E (typ.typ_all S1 S2) (typ.typ_arrow T1 T2) -> False := by
  intro h; cases h

-- No subtyping from an arrow type to a forall type
theorem no_sub_arrow_to_all {E : env} {S1 S2 T1 T2 : typ} :
  sub E (typ.typ_arrow S1 S2) (typ.typ_all T1 T2) -> False := by
  intro h; cases h

-- Shape lemma: in empty env, if the target is an arrow, the source must be an arrow
private theorem sub_empty_to_arrow {S U1 U2 : typ}
  (h : sub [] S (typ.typ_arrow U1 U2)) : ∃ S1 S2, S = typ.typ_arrow S1 S2 ∧ sub [] U1 S1 ∧ sub [] S2 U2 := by
  cases h with
  | sub_arrow E S1 S2 T1 T2 h1 h2 =>
      -- Unify indices with [] and target typ_arrow U1 U2
      exact ⟨S1, S2, rfl, h1, h2⟩
  | sub_trans_tvar U E T X hbind hsub =>
      -- Impossible in empty env
      have : False := binds_empty_inv (x := X) (b := bind.bind_sub U) (by simpa using hbind)
      exact this.elim

-- Shape lemma: in empty env, if the target is a forall, the source must be a forall
private theorem sub_empty_to_all {S U1 U2 : typ}
  (h : sub [] S (typ.typ_all U1 U2)) : ∃ S1 S2, S = typ.typ_all S1 S2 := by
  cases h with
  | sub_all L E S1 S2 T1 T2 h1 h2 =>
      -- Unify indices with [] and target typ_all U1 U2
      exact ⟨S1, S2, rfl⟩
  | sub_trans_tvar U E T X hbind hsub =>
      -- Impossible in empty env
      have : False := binds_empty_inv (x := X) (b := bind.bind_sub U) (by simpa using hbind)
      exact this.elim

theorem wft_weaken_right : ∀ (E F : env) (T : typ), wft E T -> wft (E ++ F) T := by
  intro E F T h
  induction h generalizing F with
  | wft_top E0 =>
      exact wft.wft_top (E0 ++ F)
  | wft_var U E0 X hB =>
      exact wft.wft_var U (E0 ++ F) X (by
        simpa using binds_append_left (E := E0) (F := F) (x := X) (b := bind.bind_sub U) hB)
  | wft_arrow E0 T1 T2 h1 h2 ih1 ih2 =>
      exact wft.wft_arrow (E0 ++ F) T1 T2 (ih1 F) (ih2 F)
  | wft_all L E0 T1 T2 hT1 hBody ihT1 ihBody =>
      refine wft.wft_all L (E0 ++ F) T1 T2 (ihT1 F) ?_;
      intro X hX
      -- apply weakening under the pushed binding via IH on the body
      have hWeakenBody := ihBody X hX F
      -- rewrite env shape
      simpa [List.cons_append] using hWeakenBody

theorem wft_type : ∀ E T, wft E T -> def_type T := by
  intro E T h
  induction h with
  | wft_top E =>
      exact def_type.type_top
  | wft_var U E X hbind =>
      exact def_type.type_var X
  | wft_arrow E T1 T2 h1 h2 ih1 ih2 =>
      exact def_type.type_arrow T1 T2 ih1 ih2
  | wft_all L E T1 T2 hT1 hBody ihT1 ihBody =>
      refine def_type.type_all (L:=L) (T1:=T1) (T2:=T2) ihT1 ?_;
      intro X hX
      exact ihBody X hX


-- line 1062
theorem value_regular : ∀ t, value t -> def_term t := by
  intro t h
  cases h with
  | value_abs V e1 h1 => exact h1
  | value_tabs V e1 h1 => exact h1

-- Reduction preserves regularity of terms
-- Corresponds to Coq's red_regular: red t t' -> term t ∧ term t'
theorem red_regular : ∀ t t', red t t' -> def_term t ∧ def_term t' := by
  intro t t' h
  induction h with
  | red_app_1 e1 e1' e2 hTermE2 _ ih =>
      have h1 : def_term e1 ∧ def_term e1' := ih
      exact And.intro (def_term.term_app e1 e2 h1.left hTermE2)
                      (def_term.term_app e1' e2 h1.right hTermE2)
  | red_app_2 e1 e2 e2' hValE1 _ ih =>
      have hE1 : def_term e1 := value_regular e1 hValE1
      have h2 : def_term e2 ∧ def_term e2' := ih
      exact And.intro (def_term.term_app e1 e2 hE1 h2.left)
                      (def_term.term_app e1 e2' hE1 h2.right)
  | red_tapp e1 e1' V hTypeV _ ih =>
      have h1 : def_term e1 ∧ def_term e1' := ih
      exact And.intro (def_term.term_tapp e1 V h1.left hTypeV)
                      (def_term.term_tapp e1' V h1.right hTypeV)
  | red_abs V e1 v2 hTermAbs hValV2 =>
      have hV2 : def_term v2 := value_regular v2 hValV2
      -- Use freshness from L ∪ fv_ee e1 to open and then substitute
      cases hTermAbs with
      | term_abs L V _ hVT hBody =>
          classical
          obtain ⟨x, hx⟩ := var_fresh (L ∪ fv_ee e1)
          have hxL : x ∉ L := by
            intro hmem; exact hx (Finset.mem_union.mpr (Or.inl hmem))
          have hxfree : x ∉ fv_ee e1 := by
            intro hmem; exact hx (Finset.mem_union.mpr (Or.inr hmem))
          have hBodyX : def_term (e1 open_ee_var x) := hBody x hxL
          have hSub := subst_ee_term (e1 := (e1 open_ee_var x)) (Z := x) (e2 := v2) hBodyX hV2
          have hOpen := subst_ee_intro x v2 e1 hxfree hV2
          have hOpenDef : def_term (open_ee e1 v2) := by simpa [hOpen] using hSub
          exact And.intro (def_term.term_app (trm.trm_abs V e1) v2 (def_term.term_abs L V e1 hVT hBody) hV2) hOpenDef
  | red_tabs V1 e1 V2 hTermTabs hTypeV2 =>
      cases hTermTabs with
      | term_tabs L V _ hVT hBody =>
          classical
          obtain ⟨X, hX⟩ := var_fresh (L ∪ fv_te e1)
          have hXL : X ∉ L := by
            intro hmem; exact hX (Finset.mem_union.mpr (Or.inl hmem))
          have hXfree : X ∉ fv_te e1 := by
            intro hmem; exact hX (Finset.mem_union.mpr (Or.inr hmem))
          have hBodyX : def_term (e1 open_te_var X) := hBody X hXL
          have hSub := subst_te_term (e := (e1 open_te_var X)) (Z := X) (P := V2) hBodyX hTypeV2
          have hOpen := subst_te_intro X V2 e1 hXfree hTypeV2
          have hOpenDef : def_term (open_te e1 V2) := by simpa [hOpen] using hSub
          exact And.intro (def_term.term_tapp (trm.trm_tabs V1 e1) V2 (def_term.term_tabs L V1 e1 hVT hBody) hTypeV2) hOpenDef


end Lp2lc.Active
