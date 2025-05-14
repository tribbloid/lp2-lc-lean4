/-
 * Preservation and Progress for System-F with Subtyping - Definitions
 * Brian Aydemir & Arthur Charguéraud, March 2007
 * Converted to Lean 4
 -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic

-- Define variable type as a simple alias for String
def var := String

-- Define decidable equality for variables
instance : DecidableEq var := String.decEq

-- Define Repr instance for var
instance : Repr var := inferInstanceAs (Repr String)

-- Notation for variables
variable {x y z : var}
variable {X Y Z : var}

-- Description of the Language

-- Representation of pre-types
inductive Typ : Type where
  | typ_top : Typ
  | typ_bvar : Nat → Typ
  | typ_fvar : var → Typ
  | typ_arrow : Typ → Typ → Typ
  | typ_all : Typ → Typ → Typ
  deriving Repr, BEq, Inhabited

-- Representation of pre-terms
inductive Trm : Type where
  | trm_bvar : Nat → Trm
  | trm_fvar : var → Trm
  | trm_abs : Typ → Trm → Trm
  | trm_app : Trm → Trm → Trm
  | trm_tabs : Typ → Trm → Trm
  | trm_tapp : Trm → Typ → Trm
  deriving Repr, BEq, Inhabited

-- Opening up a type binder occurring in a type
def open_tt_rec (k : Nat) (u : Typ) : Typ → Typ
  | Typ.typ_top => Typ.typ_top
  | Typ.typ_bvar i => if k = i then u else Typ.typ_bvar i
  | Typ.typ_fvar x => Typ.typ_fvar x
  | Typ.typ_arrow t1 t2 => Typ.typ_arrow (open_tt_rec k u t1) (open_tt_rec k u t2)
  | Typ.typ_all t1 t2 => Typ.typ_all (open_tt_rec k u t1) (open_tt_rec (k+1) u t2)

def open_tt (t : Typ) (u : Typ) : Typ := open_tt_rec 0 u t

-- Opening up a type binder occurring in a term
def open_te_rec (k : Nat) (u : Typ) : Trm → Trm
  | Trm.trm_bvar i => Trm.trm_bvar i
  | Trm.trm_fvar x => Trm.trm_fvar x
  | Trm.trm_abs v e1 => Trm.trm_abs (open_tt_rec k u v) (open_te_rec k u e1)
  | Trm.trm_app e1 e2 => Trm.trm_app (open_te_rec k u e1) (open_te_rec k u e2)
  | Trm.trm_tabs v e1 => Trm.trm_tabs (open_tt_rec k u v) (open_te_rec (k+1) u e1)
  | Trm.trm_tapp e1 v => Trm.trm_tapp (open_te_rec k u e1) (open_tt_rec k u v)

def open_te (t : Trm) (u : Typ) : Trm := open_te_rec 0 u t

-- Opening up a term binder occurring in a term
def open_ee_rec (k : Nat) (f : Trm) : Trm → Trm
  | Trm.trm_bvar i => if k = i then f else Trm.trm_bvar i
  | Trm.trm_fvar x => Trm.trm_fvar x
  | Trm.trm_abs v e1 => Trm.trm_abs v (open_ee_rec (k+1) f e1)
  | Trm.trm_app e1 e2 => Trm.trm_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | Trm.trm_tabs v e1 => Trm.trm_tabs v (open_ee_rec k f e1)
  | Trm.trm_tapp e1 v => Trm.trm_tapp (open_ee_rec k f e1) v

def open_ee (t : Trm) (u : Trm) : Trm := open_ee_rec 0 u t

-- Notation for opening up binders with type or term variables
def open_tt_var (t : Typ) (x : var) : Typ := open_tt t (Typ.typ_fvar x)
def open_te_var (t : Trm) (x : var) : Trm := open_te t (Typ.typ_fvar x)
def open_ee_var (t : Trm) (x : var) : Trm := open_ee t (Trm.trm_fvar x)

-- Set operations for variable sets
def var_notin (x : var) (s : Finset var) : Prop := x ∉ s

-- Types as locally closed pre-types
inductive type : Typ → Prop where
  | type_top :
      type Typ.typ_top
  | type_var : ∀ (X : var),
      type (Typ.typ_fvar X)
  | type_arrow : ∀ (T1 T2 : Typ),
      type T1 →
      type T2 →
      type (Typ.typ_arrow T1 T2)
  | type_all : ∀ (L : Finset var) (T1 T2 : Typ),
      type T1 →
      (∀ (X : var), X ∉ L → type (open_tt_var T2 X)) →
      type (Typ.typ_all T1 T2)

-- Terms as locally closed pre-terms
inductive term : Trm → Prop where
  | term_var : ∀ (x : var),
      term (Trm.trm_fvar x)
  | term_abs : ∀ (L : Finset var) (V : Typ) (e1 : Trm),
      type V →
      (∀ (x : var), x ∉ L → term (open_ee_var e1 x)) →
      term (Trm.trm_abs V e1)
  | term_app : ∀ (e1 e2 : Trm),
      term e1 →
      term e2 →
      term (Trm.trm_app e1 e2)
  | term_tabs : ∀ (L : Finset var) (V : Typ) (e1 : Trm),
      type V →
      (∀ (X : var), X ∉ L → term (open_te_var e1 X)) →
      term (Trm.trm_tabs V e1)
  | term_tapp : ∀ (e1 : Trm) (V : Typ),
      term e1 →
      type V →
      term (Trm.trm_tapp e1 V)

-- Binding are either mapping type or term variables.
-- [X ~<: T] is a subtyping assumption and [x ~: T] is a typing assumption
inductive BindType : Type where
  | bind_sub : Typ → BindType
  | bind_typ : Typ → BindType
  deriving Repr, BEq, Inhabited

-- Environment is an associative list of bindings.
def Env := List (var × BindType)

-- Define membership function for environment
def mem_env (pair : var × BindType) (env : Env) : Prop := List.elem pair env

-- Define append for environment
instance : Append Env := inferInstanceAs (Append (List (var × BindType)))

def empty : Env := []

-- Notation for binding a variable
def bind_var (x : var) (b : BindType) : var × BindType := (x, b)

-- Notation for environment concatenation (E & F means F comes after E)
def concat (E F : Env) : Env := E ++ F

-- Notation for environment concatenation
notation:60 E " & " F:60 => concat E F

-- Helper function to add a binding to an environment
def add_binding (E : Env) (binding : var × BindType) : Env := binding :: E

-- Notation for pushing a binding to an environment
def push (E : Env) (x : var) (b : BindType) : Env := (x, b) :: E

-- Notation for binding a variable with a subtyping constraint
def bind_sub_var (X : var) (T : Typ) : var × BindType := (X, BindType.bind_sub T)

-- Notation for binding a variable with a typing constraint
def bind_typ_var (x : var) (T : Typ) : var × BindType := (x, BindType.bind_typ T)

-- Notation for checking if a variable is fresh in an environment
def fresh (x : var) (E : Env) : Prop := ¬ (∃ b : BindType, mem_env (x, b) E)

notation:50 x " # " E:50 => fresh x E

-- Notation for looking up a binding in an environment
def binds (x : var) (b : BindType) (E : Env) : Prop := mem_env (x, b) E

-- Notation for subtyping and typing assumptions
notation:50 X " ~<: " T:50 => bind_sub_var X T
notation:50 x " ~: " T:50 => bind_typ_var x T

-- Notation for environment with binding
def env_bind_sub (E : Env) (x : var) (T : Typ) : Env := push E x (BindType.bind_sub T)
def env_bind_typ (E : Env) (x : var) (T : Typ) : Env := push E x (BindType.bind_typ T)

notation:60 E " & " x " ~<: " T:60 => env_bind_sub E x T
notation:60 E " & " x " ~: " T:60 => env_bind_typ E x T

-- Well-formedness of a pre-type T in an environment E:
-- all the type variables of T must be bound via a
-- subtyping relation in E. This predicate implies
-- that T is a type
inductive wft : Env → Typ → Prop where
  | wft_top : ∀ (E : Env),
      wft E Typ.typ_top
  | wft_var : ∀ (U : Typ) (E : Env) (X : var),
      binds X (BindType.bind_sub U) E →
      wft E (Typ.typ_fvar X)
  | wft_arrow : ∀ (E : Env) (T1 T2 : Typ),
      wft E T1 →
      wft E T2 →
      wft E (Typ.typ_arrow T1 T2)
  | wft_all : ∀ (L : Finset var) (E : Env) (T1 T2 : Typ),
      wft E T1 →
      (∀ (X : var), X ∉ L →
        wft (env_bind_sub E X T1) (open_tt_var T2 X)) →
      wft E (Typ.typ_all T1 T2)

-- A environment E is well-formed if it contains no duplicate bindings
-- and if each type in it is well-formed with respect to the environment
-- it is pushed on to.

-- First, define the ok predicate for environments with no duplicates
inductive ok : Env → Prop where
  | ok_empty :
      ok empty
  | ok_push : ∀ (E : Env) (x : var) (b : BindType),
      ok E → x # E → ok (push E x b)

-- Then define the well-formed environment predicate
inductive okt : Env → Prop where
  | okt_empty :
      okt empty
  | okt_sub : ∀ (E : Env) (X : var) (T : Typ),
      okt E → wft E T → X # E → okt (env_bind_sub E X T)
  | okt_typ : ∀ (E : Env) (x : var) (T : Typ),
      okt E → wft E T → x # E → okt (env_bind_typ E x T)

-- Subtyping relation
inductive sub : Env → Typ → Typ → Prop where
  | sub_top : ∀ (E : Env) (S : Typ),
      okt E →
      wft E S →
      sub E S Typ.typ_top
  | sub_refl_tvar : ∀ (E : Env) (X : var),
      okt E →
      wft E (Typ.typ_fvar X) →
      sub E (Typ.typ_fvar X) (Typ.typ_fvar X)
  | sub_trans_tvar : ∀ (U : Typ) (E : Env) (T : Typ) (X : var),
      binds X (BindType.bind_sub U) E →
      sub E U T →
      sub E (Typ.typ_fvar X) T
  | sub_arrow : ∀ (E : Env) (S1 S2 T1 T2 : Typ),
      sub E T1 S1 →
      sub E S2 T2 →
      sub E (Typ.typ_arrow S1 S2) (Typ.typ_arrow T1 T2)
  | sub_all : ∀ (L : Finset var) (E : Env) (S1 S2 T1 T2 : Typ),
      sub E T1 S1 →
      (∀ (X : var), X ∉ L →
          sub (env_bind_sub E X T1) (open_tt_var S2 X) (open_tt_var T2 X)) →
      sub E (Typ.typ_all S1 S2) (Typ.typ_all T1 T2)

-- Typing relation
inductive typing : Env → Trm → Typ → Prop where
  | typing_var : ∀ (E : Env) (x : var) (T : Typ),
      okt E →
      binds x (BindType.bind_typ T) E →
      typing E (Trm.trm_fvar x) T
  | typing_abs : ∀ (L : Finset var) (E : Env) (V : Typ) (e1 : Trm) (T1 : Typ),
      (∀ (x : var), x ∉ L →
        typing (env_bind_typ E x V) (open_ee_var e1 x) T1) →
      typing E (Trm.trm_abs V e1) (Typ.typ_arrow V T1)
  | typing_app : ∀ (T1 : Typ) (E : Env) (e1 e2 : Trm) (T2 : Typ),
      typing E e1 (Typ.typ_arrow T1 T2) →
      typing E e2 T1 →
      typing E (Trm.trm_app e1 e2) T2
  | typing_tabs : ∀ (L : Finset var) (E : Env) (V : Typ) (e1 : Trm) (T1 : Typ),
      (∀ (X : var), X ∉ L →
        typing (env_bind_sub E X V) (open_te_var e1 X) (open_tt_var T1 X)) →
      typing E (Trm.trm_tabs V e1) (Typ.typ_all V T1)
  | typing_tapp : ∀ (T1 : Typ) (E : Env) (e1 : Trm) (T : Typ) (T2 : Typ),
      typing E e1 (Typ.typ_all T1 T2) →
      sub E T T1 →
      typing E (Trm.trm_tapp e1 T) (open_tt T2 T)
  | typing_sub : ∀ (S : Typ) (E : Env) (e : Trm) (T : Typ),
      typing E e S →
      sub E S T →
      typing E e T

-- Values
inductive value : Trm → Prop where
  | value_abs : ∀ (V : Typ) (e1 : Trm),
      term (Trm.trm_abs V e1) →
      value (Trm.trm_abs V e1)
  | value_tabs : ∀ (V : Typ) (e1 : Trm),
      term (Trm.trm_tabs V e1) →
      value (Trm.trm_tabs V e1)

-- One-step reduction
inductive red : Trm → Trm → Prop where
  | red_app_1 : ∀ (e1 e1' e2 : Trm),
      term e2 →
      red e1 e1' →
      red (Trm.trm_app e1 e2) (Trm.trm_app e1' e2)
  | red_app_2 : ∀ (e1 e2 e2' : Trm),
      value e1 →
      red e2 e2' →
      red (Trm.trm_app e1 e2) (Trm.trm_app e1 e2')
  | red_tapp : ∀ (e1 e1' : Trm) (V : Typ),
      type V →
      red e1 e1' →
      red (Trm.trm_tapp e1 V) (Trm.trm_tapp e1' V)
  | red_abs : ∀ (V : Typ) (e1 v2 : Trm),
      term (Trm.trm_abs V e1) →
      value v2 →
      red (Trm.trm_app (Trm.trm_abs V e1) v2) (open_ee e1 v2)
  | red_tabs : ∀ (V1 : Typ) (e1 : Trm) (V2 : Typ),
      term (Trm.trm_tabs V1 e1) →
      type V2 →
      red (Trm.trm_tapp (Trm.trm_tabs V1 e1) V2) (open_te e1 V2)

-- Our goal is to prove preservation and progress
-- These are the statements of the theorems we will prove
def preservation_statement : Prop := ∀ (E : Env) (e e' : Trm) (T : Typ),
  typing E e T → red e e' → typing E e' T

def progress_statement : Prop := ∀ (e : Trm) (T : Typ),
  typing empty e T → value e ∨ (∃ e', red e e')

-- Additional Definitions Used in the Proofs

-- Computing free type variables in a type
def fv_tt : Typ → Finset var
  | Typ.typ_top => {}
  | Typ.typ_bvar _ => {}
  | Typ.typ_fvar X => {X}
  | Typ.typ_arrow T1 T2 => fv_tt T1 ∪ fv_tt T2
  | Typ.typ_all T1 T2 => fv_tt T1 ∪ fv_tt T2

-- Computing free type variables in a term
def fv_te : Trm → Finset var
  | Trm.trm_bvar _ => {}
  | Trm.trm_fvar _ => {}
  | Trm.trm_abs V e1 => fv_tt V ∪ fv_te e1
  | Trm.trm_app e1 e2 => fv_te e1 ∪ fv_te e2
  | Trm.trm_tabs V e1 => fv_tt V ∪ fv_te e1
  | Trm.trm_tapp e1 V => fv_tt V ∪ fv_te e1

-- Computing free term variables in a term
def fv_ee : Trm → Finset var
  | Trm.trm_bvar _ => {}
  | Trm.trm_fvar x => {x}
  | Trm.trm_abs _ e1 => fv_ee e1
  | Trm.trm_app e1 e2 => fv_ee e1 ∪ fv_ee e2
  | Trm.trm_tabs _ e1 => fv_ee e1
  | Trm.trm_tapp e1 _ => fv_ee e1

-- Substitution for free type variables in types
def subst_tt (Z : var) (U : Typ) : Typ → Typ
  | Typ.typ_top => Typ.typ_top
  | Typ.typ_bvar J => Typ.typ_bvar J
  | Typ.typ_fvar X => if X = Z then U else Typ.typ_fvar X
  | Typ.typ_arrow T1 T2 => Typ.typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | Typ.typ_all T1 T2 => Typ.typ_all (subst_tt Z U T1) (subst_tt Z U T2)

-- Substitution for free type variables in terms
def subst_te (Z : var) (U : Typ) : Trm → Trm
  | Trm.trm_bvar i => Trm.trm_bvar i
  | Trm.trm_fvar x => Trm.trm_fvar x
  | Trm.trm_abs V e1 => Trm.trm_abs (subst_tt Z U V) (subst_te Z U e1)
  | Trm.trm_app e1 e2 => Trm.trm_app (subst_te Z U e1) (subst_te Z U e2)
  | Trm.trm_tabs V e1 => Trm.trm_tabs (subst_tt Z U V) (subst_te Z U e1)
  | Trm.trm_tapp e1 V => Trm.trm_tapp (subst_te Z U e1) (subst_tt Z U V)

-- Substitution for free term variables in terms
def subst_ee (z : var) (u : Trm) : Trm → Trm
  | Trm.trm_bvar i => Trm.trm_bvar i
  | Trm.trm_fvar x => if x = z then u else Trm.trm_fvar x
  | Trm.trm_abs V e1 => Trm.trm_abs V (subst_ee z u e1)
  | Trm.trm_app e1 e2 => Trm.trm_app (subst_ee z u e1) (subst_ee z u e2)
  | Trm.trm_tabs V e1 => Trm.trm_tabs V (subst_ee z u e1)
  | Trm.trm_tapp e1 V => Trm.trm_tapp (subst_ee z u e1) V

-- Substitution for free type variables in environment
def subst_tb (Z : var) (P : Typ) : BindType → BindType
  | BindType.bind_sub T => BindType.bind_sub (subst_tt Z P T)
  | BindType.bind_typ T => BindType.bind_typ (subst_tt Z P T)

-- Map substitution over an environment
def map_subst_tb (Z : var) (P : Typ) (E : Env) : Env :=
  List.map (fun (pair : var × BindType) => (pair.1, subst_tb Z P pair.2)) E

/-
 * Properties of Substitutions
 -/

-- Properties of type substitution in type

-- Substitution on indices is identity on well-formed terms
theorem open_tt_rec_type_core : ∀ (T : Typ) (j : Nat) (V U : Typ) (i : Nat), i ≠ j →
  open_tt_rec j V T = open_tt_rec i U (open_tt_rec j V T) →
  T = open_tt_rec i U T :=
  sorry

theorem open_tt_rec_type : ∀ (T : Typ) (U : Typ),
  type T → ∀ (k : Nat), T = open_tt_rec k U T :=
  sorry

-- Substitution for a fresh name is identity
theorem subst_tt_fresh : ∀ (Z : var) (U : Typ) (T : Typ),
  Z ∉ fv_tt T → subst_tt Z U T = T :=
  sorry

-- Substitution distributes on the open operation
theorem subst_tt_open_tt_rec : ∀ (T1 T2 : Typ) (X : var) (P : Typ) (n : Nat), type P →
  subst_tt X P (open_tt_rec n T2 T1) =
  open_tt_rec n (subst_tt X P T2) (subst_tt X P T1) :=
  sorry

theorem subst_tt_open_tt : ∀ (T1 T2 : Typ) (X : var) (P : Typ), type P →
  subst_tt X P (open_tt T1 T2) =
  open_tt (subst_tt X P T1) (subst_tt X P T2) :=
  sorry

-- Substitution and open_var for distinct names commute
theorem subst_tt_open_tt_var : ∀ (X Y : var) (U T : Typ), Y ≠ X → type U →
  subst_tt X U (open_tt_var T Y) = open_tt_var (subst_tt X U T) Y :=
  sorry

-- Opening up a body t with a type u is the same as opening
-- up the abstraction with a fresh name x and then substituting u for x
theorem subst_tt_intro : ∀ (X : var) (T2 U : Typ),
  X ∉ fv_tt T2 → type U →
  open_tt T2 U = subst_tt X U (open_tt_var T2 X) :=
  sorry

-- Properties of type substitution in terms
theorem open_te_rec_term_core : ∀ (e : Trm) (j : Nat) (u : Trm) (i : Nat) (P : Typ),
  open_ee_rec j u e = open_te_rec i P (open_ee_rec j u e) →
  e = open_te_rec i P e :=
  sorry

theorem open_te_rec_type_core : ∀ (e : Trm) (j : Nat) (Q : Typ) (i : Nat) (P : Typ), i ≠ j →
  open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) →
  e = open_te_rec i P e :=
  sorry

theorem open_te_rec_term : ∀ (e : Trm) (U : Typ),
  term e → ∀ (k : Nat), e = open_te_rec k U e :=
  sorry

-- Substitution for a fresh name is identity
theorem subst_te_fresh : ∀ (X : var) (U : Typ) (e : Trm),
  X ∉ fv_te e → subst_te X U e = e :=
  sorry

-- Substitution distributes on the open operation
theorem subst_te_open_te : ∀ (e : Trm) (T : Typ) (X : var) (U : Typ), type U →
  subst_te X U (open_te e T) =
  open_te (subst_te X U e) (subst_tt X U T) :=
  sorry

-- Substitution and open_var for distinct names commute
theorem subst_te_open_te_var : ∀ (X Y : var) (U : Typ) (e : Trm), Y ≠ X → type U →
  subst_te X U (open_te_var e Y) = open_te_var (subst_te X U e) Y :=
  sorry

-- Opening up a body t with a type u is the same as opening
-- up the abstraction with a fresh name x and then substituting u for x
theorem subst_te_intro : ∀ (X : var) (U : Typ) (e : Trm),
  X ∉ fv_te e → type U →
  open_te e U = subst_te X U (open_te_var e X) :=
  sorry

-- Properties of term substitution in terms
theorem open_ee_rec_term_core : ∀ (e : Trm) (j : Nat) (v u : Trm) (i : Nat), i ≠ j →
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) →
  e = open_ee_rec i u e :=
  sorry

theorem open_ee_rec_term : ∀ (u e : Trm),
  term e → ∀ (k : Nat), e = open_ee_rec k u e :=
  sorry

-- Substitution for a fresh name is identity
theorem subst_ee_fresh : ∀ (x : var) (u : Trm) (e : Trm),
  x ∉ fv_ee e → subst_ee x u e = e :=
  sorry

-- Substitution distributes on the open operation
theorem subst_ee_open_ee : ∀ (t1 t2 u : Trm) (x : var), term u →
  subst_ee x u (open_ee t1 t2) =
  open_ee (subst_ee x u t1) (subst_ee x u t2) :=
  sorry

-- Substitution and open_var for distinct names commute
theorem subst_ee_open_ee_var : ∀ (x y : var) (u e : Trm), y ≠ x → term u →
  subst_ee x u (open_ee_var e y) = open_ee_var (subst_ee x u e) y :=
  sorry

-- Opening up a body t with a term u is the same as opening
-- up the abstraction with a fresh name x and then substituting u for x
theorem subst_ee_intro : ∀ (x : var) (u e : Trm),
  x ∉ fv_ee e → term u →
  open_ee e u = subst_ee x u (open_ee_var e x) :=
  sorry

-- Interactions between type substitutions in terms and opening
-- with term variables in terms
theorem subst_te_open_ee_var : ∀ (Z : var) (P : Typ) (x : var) (e : Trm),
  subst_te Z P (open_ee_var e x) = open_ee_var (subst_te Z P e) x :=
  sorry

-- Interactions between term substitutions in terms and opening
-- with type variables in terms
theorem subst_ee_open_te_var : ∀ (z : var) (u : Trm) (e : Trm) (X : var), term u →
  subst_ee z u (open_te_var e X) = open_te_var (subst_ee z u e) X :=
  sorry

-- Substitutions preserve local closure
theorem subst_tt_type : ∀ (T : Typ) (Z : var) (P : Typ),
  type T → type P → type (subst_tt Z P T) :=
  sorry

theorem subst_te_term : ∀ (e : Trm) (Z : var) (P : Typ),
  term e → type P → term (subst_te Z P e) :=
  sorry

theorem subst_ee_term : ∀ (e1 : Trm) (Z : var) (e2 : Trm),
  term e1 → term e2 → term (subst_ee Z e2 e1) :=
  sorry

/-
 * Properties of well-formedness of a type in an environment
 -/

-- If a type is well-formed in an environment then it is locally closed
theorem wft_type : ∀ (E : Env) (T : Typ),
  wft E T → type T :=
  sorry

-- Through weakening
theorem wft_weaken : ∀ (G : Env) (T : Typ) (E F : Env),
  wft (concat E G) T →
  ok (concat E (concat F G)) →
  wft (concat E (concat F G)) T :=
  sorry

-- Through narrowing
theorem wft_narrow : ∀ (V : Typ) (F : Env) (U : Typ) (T : Typ) (E : Env) (X : var),
  wft (concat E (concat (push empty X (BindType.bind_sub V)) F)) T →
  ok (concat E (concat (push empty X (BindType.bind_sub U)) F)) →
  wft (concat E (concat (push empty X (BindType.bind_sub U)) F)) T :=
  sorry

-- Through strengthening
theorem wft_strengthen : ∀ (E F : Env) (x : var) (U : Typ) (T : Typ),
  wft (concat E (concat (push empty x (BindType.bind_typ U)) F)) T → wft (concat E F) T :=
  sorry

-- Map substitution over environment bindings is already defined above

-- Through type substitution
theorem wft_subst_tb : ∀ (F : Env) (Q : Typ) (E : Env) (Z : var) (P : Typ) (T : Typ),
  wft (concat E (concat (push empty Z (BindType.bind_sub Q)) F)) T →
  wft E P →
  ok (concat E (map_subst_tb Z P F)) →
  wft (concat E (map_subst_tb Z P F)) (subst_tt Z P T) :=
  sorry

-- Through type reduction
theorem wft_open : ∀ (E : Env) (U : Typ) (T1 T2 : Typ),
  ok E →
  wft E (Typ.typ_all T1 T2) →
  wft E U →
  wft E (open_tt T2 U) :=
  sorry

/-
 * Properties of subtyping
 -/

-- Reflexivity of subtyping
theorem sub_reflexivity : ∀ (E : Env) (T : Typ),
  wft E T → sub E T T :=
  sorry

-- Transitivity of subtyping
theorem sub_transitivity : ∀ (E : Env) (S T U : Typ),
  sub E S T → sub E T U → sub E S U :=
  sorry

-- Narrowing of subtyping
theorem sub_narrowing : ∀ (F : Env) (X : var) (P Q : Typ) (E : Env) (S T : Typ),
  sub (concat E (concat (push empty X (BindType.bind_sub Q)) F)) S T →
  sub E P Q →
  ok (concat E (concat (push empty X (BindType.bind_sub P)) F)) →
  sub (concat E (concat (push empty X (BindType.bind_sub P)) F)) S T :=
  sorry

-- Weakening of subtyping
theorem sub_weakening : ∀ (G : Env) (S T : Typ) (E F : Env),
  sub (concat E G) S T →
  ok (concat E (concat F G)) →
  sub (concat E (concat F G)) S T :=
  sorry

/-
 * Properties of typing
 -/

-- Weakening of typing
theorem typing_weakening : ∀ (G : Env) (e : Trm) (T : Typ) (E F : Env),
  typing (concat E G) e T →
  ok (concat E (concat F G)) →
  typing (concat E (concat F G)) e T :=
  sorry

-- Strengthening of typing for type variables
theorem typing_strengthening_typ : ∀ (E F : Env) (x : var) (U : Typ) (e : Trm) (T : Typ),
  typing (concat E (concat (push empty x (BindType.bind_typ U)) F)) e T →
  x ∉ fv_ee e →
  typing (concat E F) e T :=
  sorry

-- Strengthening of typing for term variables
theorem typing_strengthening_sub : ∀ (E F : Env) (X : var) (U : Typ) (e : Trm) (T : Typ),
  typing (concat E (concat (push empty X (BindType.bind_sub U)) F)) e T →
  X ∉ fv_te e → X ∉ fv_tt T →
  typing (concat E F) e T :=
  sorry

-- Narrowing of typing
theorem typing_narrowing : ∀ (F : Env) (X : var) (P Q : Typ) (E : Env) (e : Trm) (T : Typ),
  typing (concat E (concat (push empty X (BindType.bind_sub Q)) F)) e T →
  sub E P Q →
  ok (concat E (concat (push empty X (BindType.bind_sub P)) F)) →
  typing (concat E (concat (push empty X (BindType.bind_sub P)) F)) e T :=
  sorry

-- Type substitution preserves typing
theorem typing_through_subst_tt : ∀ (F : Env) (X : var) (Q : Typ) (E : Env) (e : Trm) (T P : Typ),
  typing (concat E (concat (push empty X (BindType.bind_sub Q)) F)) e T →
  sub E P Q →
  typing (concat E (map_subst_tb X P F)) (subst_te X P e) (subst_tt X P T) :=
  sorry

-- Term substitution preserves typing
theorem typing_through_subst_ee : ∀ (F : Env) (x : var) (U : Typ) (E : Env) (e : Trm) (T : Typ) (u : Trm),
  typing (concat E (concat (push empty x (BindType.bind_typ U)) F)) e T →
  typing E u U →
  typing (concat E F) (subst_ee x u e) T :=
  sorry

/-
 * Progress and preservation
 -/

-- Progress: a well-typed term is either a value or can take a step
theorem progress_theorem : ∀ (e : Trm) (T : Typ),
  typing empty e T → value e ∨ (∃ e', red e e') :=
  sorry

-- Preservation: if a well-typed term takes a step, the resulting term has the same type
theorem preservation_theorem : ∀ (e e' : Trm) (T : Typ),
  typing empty e T → red e e' → typing empty e' T :=
  sorry
