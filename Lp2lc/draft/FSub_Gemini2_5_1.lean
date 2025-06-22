/-
system prompt

# Environment
- The code is written in Lean 4.18
- The build system is lake
- Build errors can observed by running "lake build"
<!-- - do not run terminal command to check errors -->
<!-- - all compilation errors are displayed in LSP -->

# Code Style
- every lean 4 definition (variables, functions, types) should have identical name and case to its counterpart in Rocq definition
- Hint in Rocq file should be converted to a AESOP annotation or macro tactic definition
- built-in tactics and AESOP is preferred for automated proof search

# Workflow
- write 1 definition at a time, starting from top to bottom
- each definition should be accompanied by a comment with line number that indicates the Rocq definition it is based on
- compile often to make sure that the definition has no error
- do not use "sorry"
- do not use "open"
- do not define new axiom
- do not introduce new dependency
- prefer definition in Mathlib

<!-- # Caution: -->
<!-- - Std.Data is now replaced by Mathlib.Data in lean 4
- {} should be used to represent an empty Finset -->

-/

import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic

import Aesop
import Mathlib.Data.Finset.Basic

-- From Fsub.v:13
/-- Representation of pre-types -/
@[aesop safe constructors]
inductive typ where
  | typ_top   : typ
  | typ_bvar  : Nat → typ
  | typ_fvar  : String → typ  -- Assuming 'var' from Coq's LibLN is represented as String
  | typ_arrow : typ → typ → typ
  | typ_all   : typ → typ → typ
  deriving BEq, DecidableEq

-- From Fsub.v:22
/-- Representation of pre-terms -/
@[aesop safe constructors]
inductive trm where
  | trm_bvar : Nat → trm
  | trm_fvar : String → trm  -- Assuming 'var' from Coq's LibLN is represented as String
  | trm_abs  : typ → trm → trm
  | trm_app  : trm → trm → trm
  | trm_tabs : typ → trm → trm
  | trm_tapp : trm → typ → trm

-- From Fsub.v:32
/-- Opening up a type binder occuring in a type -/
def open_tt_rec (K : Nat) (U : typ) (T : typ) : typ :=
  match T with
  | typ.typ_top         => typ.typ_top
  | typ.typ_bvar J      => if K = J then U else (typ.typ_bvar J)
  | typ.typ_fvar X      => typ.typ_fvar X
  | typ.typ_arrow T1 T2 => typ.typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ.typ_all T1 T2   => typ.typ_all (open_tt_rec K U T1) (open_tt_rec (K + 1) U T2)

-- From Fsub.v:41
@[simp]
def open_tt (T : typ) (U : typ) : typ := open_tt_rec 0 U T

-- From Fsub.v:47
/-- Opening up a type binder occuring in a term -/
def open_te_rec (K : Nat) (U : typ) (e : trm) : trm :=
  match e with
  | trm.trm_bvar i    => trm.trm_bvar i
  | trm.trm_fvar x    => trm.trm_fvar x
  | trm.trm_abs V e1  => trm.trm_abs  (open_tt_rec K U V)  (open_te_rec K U e1)
  | trm.trm_app e1 e2 => trm.trm_app  (open_te_rec K U e1) (open_te_rec K U e2)
  | trm.trm_tabs V e1 => trm.trm_tabs (open_tt_rec K U V)  (open_te_rec (K + 1) U e1)
  | trm.trm_tapp e1 V => trm.trm_tapp (open_te_rec K U e1) (open_tt_rec K U V)

-- From Fsub.v:56
@[simp]
def open_te (t : trm) (U : typ) : trm := open_te_rec 0 U t

-- From Fsub.v:60
/-- Opening up a term binder occuring in a term -/
def open_ee_rec (k : Nat) (f : trm) (e : trm) : trm :=
  match e with
  | trm.trm_bvar i    => if k = i then f else (trm.trm_bvar i)
  | trm.trm_fvar x    => trm.trm_fvar x
  | trm.trm_abs V e1  => trm.trm_abs V (open_ee_rec (k + 1) f e1)
  | trm.trm_app e1 e2 => trm.trm_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | trm.trm_tabs V e1 => trm.trm_tabs V (open_ee_rec k f e1)
  | trm.trm_tapp e1 V => trm.trm_tapp (open_ee_rec k f e1) V

-- From Fsub.v:70
@[simp]
def open_ee (t : trm) (u : trm) : trm := open_ee_rec 0 u t

-- From Fsub.v:74
/-- Notation for opening up binders with type or term variables -/
notation:67 T " open_tt_var " X => open_tt T (typ.typ_fvar X)

-- From Fsub.v:75
notation:67 t " open_te_var " X => open_te t (typ.typ_fvar X)

-- From Fsub.v:76
notation:67 t " open_ee_var " x => open_ee t (trm.trm_fvar x)

-- From Fsub.v:81
/-- Types as locally closed pre-types -/
inductive type : typ → Prop where
  | type_top :
      type typ.typ_top
  | type_var (X : String) :
      type (typ.typ_fvar X)
  | type_arrow (T1 T2 : typ) :
      type T1 →
      type T2 →
      type (typ.typ_arrow T1 T2)
  | type_all (L : List String) (T1 T2 : typ) :
      type T1 →
      (∀ (X : String), X ∉ L → type (T2 open_tt_var X)) →
      type (typ.typ_all T1 T2)

-- From Fsub.v:95
/-- Terms as locally closed pre-terms -/
inductive term : trm → Prop where
  | term_var (x : String) :
      term (trm.trm_fvar x)
  | term_abs (L : List String) (V : typ) (e1 : trm) :
      type V →
      (∀ (x : String), x ∉ L → term (e1 open_ee_var x)) →
      term (trm.trm_abs V e1)
  | term_app (e1 e2 : trm) :
      term e1 →
      term e2 →
      term (trm.trm_app e1 e2)
  | term_tabs (L : List String) (V : typ) (e1 : trm) :
      type V →
      (∀ (X : String), X ∉ L → term (e1 open_te_var X)) →
      term (trm.trm_tabs V e1)
  | term_tapp (e1 : trm) (V : typ) :
      term e1 →
      type V →
      term (trm.trm_tapp e1 V)

-- From Fsub.v:119
/-- Binding are either mapping type or term variables.
 [X ~<: T] is a subtyping asumption and [x ~: T] is
 a typing assumption -/
inductive bind where
  | bind_sub : typ → bind
  | bind_typ : typ → bind
  deriving BEq, DecidableEq

-- From Fsub.v:123
notation:23 X " ~<: " T => (X, bind.bind_sub T)

-- From Fsub.v:125
notation:23 x " ~: " T  => (x, bind.bind_typ T)

-- From Fsub.v:130
/-- Environment is an associative list of bindings. -/
def env := List (String × bind)

instance instBEqProdStringBind : BEq (String × bind) :=
  ⟨fun p1 p2 => p1.fst == p2.fst && p1.snd == p2.snd⟩

-- From Fsub.v:139
/-- Well-formedness of a pre-type T in an environment E:
  all the type variables of T must be bound via a
  subtyping relation in E. This predicates implies
  that T is a type -/
@[aesop safe constructors]
inductive wft : env → typ → Prop where
  | wft_top (E : env) :
      wft E typ.typ_top
  | wft_var (U : typ) (E : env) (X : String) :
      List.Mem (X, bind.bind_sub U) E →  -- Corresponds to 'binds X (bind_sub U) E'
      wft E (typ.typ_fvar X)
  | wft_arrow (E : env) (T1 T2 : typ) :
      wft E T1 →
      wft E T2 →
      wft E (typ.typ_arrow T1 T2)
  | wft_all (L : List String) (E : env) (T1 T2 : typ) :
      wft E T1 →
      (∀ (X : String), X ∉ L → wft ((X, bind.bind_sub T1) :: E) (T2 open_tt_var X)) →
      wft E (typ.typ_all T1 T2)

-- From Fsub.v:158
/-- A environment E is well-formed if it contains no duplicate bindings
  and if each type in it is well-formed with respect to the environment
  it is pushed on to. -/
@[aesop safe constructors]
inductive okt : env → Prop where
  | okt_empty :
      okt []
  | okt_sub (E : env) (X : String) (T : typ) :
      okt E →
      wft E T →
      ¬(E.any (fun entry => entry.fst = X)) →  -- X is not a key in E
      okt ((X, bind.bind_sub T) :: E)
  | okt_typ (E : env) (x : String) (T : typ) :
      okt E →
      wft E T →
      ¬(E.any (fun entry => entry.fst = x)) →  -- x is not a key in E
      okt ((x, bind.bind_typ T) :: E)

-- From Fsub.v:375
lemma unique_empty_ok : okt [] :=
  okt.okt_empty

-- From Fsub.v:169
/-- Subtyping relation -/
@[aesop safe constructors]
inductive sub : env → typ → typ → Prop where
  | sub_top (E : env) (S : typ) :
      okt E →
      wft E S →
      sub E S typ.typ_top
  | sub_refl (E : env) (T : typ) :
      okt E →
      wft E T →
      sub E T T
  | sub_refl_tvar (E : env) (X : String) :
      okt E →
      wft E (typ.typ_fvar X) →
      sub E (typ.typ_fvar X) (typ.typ_fvar X)
  | sub_trans_tvar (U : typ) (E : env) (T : typ) (X : String) :
      List.Mem (X, bind.bind_sub U) E →
      sub E U T →
      sub E (typ.typ_fvar X) T
  | sub_arrow (E : env) (S1 S2 T1 T2 : typ) :
      sub E T1 S1 →
      sub E S2 T2 →
      sub E (typ.typ_arrow S1 S2) (typ.typ_arrow T1 T2)
  | sub_all (L : List String) (E : env) (S1 S2 T1 T2 : typ) :
      sub E T1 S1 →
      (∀ (X : String), X ∉ L →
        sub ((X, bind.bind_sub T1) :: E) (S2 open_tt_var X) (T2 open_tt_var X)) →
      sub E (typ.typ_all S1 S2) (typ.typ_all T1 T2)

-- From Fsub.v:379
lemma sub_refl_ok (E : env) (S : typ) :
  okt E → wft E S → sub E S S :=
  fun h_okt h_wft => sub.sub_refl E S h_okt h_wft

-- From Fsub.v:194
/-- Typing relation -/
@[aesop safe constructors]
inductive typing : env → trm → typ → Prop where
  | typing_var (E : env) (x : String) (T : typ) :
      okt E →
      List.Mem (x, bind.bind_typ T) E →
      typing E (trm.trm_fvar x) T
  | typing_abs (L : List String) (E : env) (V : typ) (e1 : trm) (T1 : typ) :
      (∀ (x : String), x ∉ L →
        typing ((x, bind.bind_typ V) :: E) (e1 open_ee_var x) T1) →
      typing E (trm.trm_abs V e1) (typ.typ_arrow V T1)
  | typing_app (T1 : typ) (E : env) (e1 e2 : trm) (T2 : typ) :
      typing E e1 (typ.typ_arrow T1 T2) →
      typing E e2 T1 →
      typing E (trm.trm_app e1 e2) T2
  | typing_tabs (L : List String) (E : env) (V : typ) (e1 : trm) (T1 : typ) :
      (∀ (X : String), X ∉ L →
        typing ((X, bind.bind_sub V) :: E) (e1 open_te_var X) (T1 open_tt_var X)) →
      typing E (trm.trm_tabs V e1) (typ.typ_all V T1)
  | typing_tapp (T1 : typ) (E : env) (e1 : trm) (T T2 : typ) :
      typing E e1 (typ.typ_all T1 T2) →
      sub E T T1 →
      typing E (trm.trm_tapp e1 T) (open_tt T2 T)
  | typing_sub (S : typ) (E : env) (e : trm) (T : typ) :
      typing E e S →
      sub E S T →
      typing E e T

-- From Fsub.v:390
lemma typing_abs_var_inv
    (E_ctx : env) (V_abs_ty : typ) (e_abs_body : trm) (U_arrow_cod : typ)
    (h_typing_abs_arrow : typing E_ctx (trm.trm_abs V_abs_ty e_abs_body) (typ.typ_arrow V_abs_ty U_arrow_cod))
    : (∃ (L_from_derivation : List String), ∀ (x_fresh : String), x_fresh ∉ L_from_derivation →
        typing ((x_fresh, bind.bind_typ V_abs_ty) :: E_ctx) (open_ee_var e_abs_body x_fresh) U_arrow_cod) :=
  by
  cases h_typing_abs_arrow with
  | typing_abs L_rule E_rule V_rule e_rule T_rule h_body_premise_rule =>
    exists L_rule
    intro x_fresh hx_fresh_notin_L_rule
    exact h_body_premise_rule x_fresh hx_fresh_notin_L_rule

-- From Fsub.v:222
/-- Values -/
@[aesop safe constructors]
inductive value : trm → Prop where
  | value_abs (V : typ) (e1 : trm) :
      value (trm.trm_abs V e1)
  | value_tabs (V : typ) (e1 : trm) :
      value (trm.trm_tabs V e1)

-- From Fsub.v:230
/-- One-step reduction -/
@[aesop safe constructors]
inductive red : trm → trm → Prop where
  | red_app_1 (e1 e1' e2 : trm) :
      red e1 e1' →
      red (trm.trm_app e1 e2) (trm.trm_app e1' e2)
  | red_app_2 (e1 e2 e2' : trm) :
      value e1 →
      red e2 e2' →
      red (trm.trm_app e1 e2) (trm.trm_app e1 e2')
  | red_tapp (e1 e1' : trm) (V : typ) :
      red e1 e1' →
      red (trm.trm_tapp e1 V) (trm.trm_tapp e1' V)
  | red_abs (V : typ) (e1 : trm) (v2 : trm) :
      value v2 →
      red (trm.trm_app (trm.trm_abs V e1) v2) (open_ee e1 v2)
  | red_tabs (V1 : typ) (e1 : trm) (V2 : typ) :
      red (trm.trm_tapp (trm.trm_tabs V1 e1) V2) (open_te e1 V2)

-- From Fsub.v:254
/-- Our goal is to prove preservation and progress -/
def preservation : Prop :=
  ∀ (E : env) (e e' : trm) (T : typ),
    typing E e T →
    red e e' →
    typing E e' T

-- From Fsub.v:259
def progress : Prop :=
  ∀ (e : trm) (T : typ),
    typing [] e T →
    (value e ∨ (∃ (e' : trm), red e e'))

-- From Fsub.v:272
/-- Computing free type variables in a type -/
def fv_tt : typ → Finset String :=
  fun T =>
  match T with
  | typ.typ_top        => ∅
  | typ.typ_bvar _J    => ∅
  | typ.typ_fvar X     => {X}
  | typ.typ_arrow T1 T2 => (fv_tt T1) ∪ (fv_tt T2)
  | typ.typ_all T1 T2   => (fv_tt T1) ∪ (fv_tt T2)

-- From Fsub.v:283
/-- Computing free type variables in a term -/
def fv_te : trm → Finset String :=
  fun e =>
  match e with
  | trm.trm_bvar _i   => ∅
  | trm.trm_fvar _x   => ∅
  | trm.trm_abs V e1  => (fv_tt V) ∪ (fv_te e1)
  | trm.trm_app e1 e2 => (fv_te e1) ∪ (fv_te e2)
  | trm.trm_tabs V e1 => (fv_tt V) ∪ (fv_te e1)
  | trm.trm_tapp e1 V => (fv_tt V) ∪ (fv_te e1)

-- From Fsub.v:295
/-- Computing free term variables in a term -/
def fv_ee : trm → Finset String :=
  fun e =>
  match e with
  | trm.trm_bvar _i   => ∅
  | trm.trm_fvar x    => {x}
  | trm.trm_abs _V e1 => (fv_ee e1) -- Term variable binders are handled by open_ee/open_ee_var for specific bound variables
  | trm.trm_app e1 e2 => (fv_ee e1) ∪ (fv_ee e2)
  | trm.trm_tabs _V e1 => (fv_ee e1) -- Type abstractions do not bind term variables
  | trm.trm_tapp e1 _V => (fv_ee e1)

-- From Fsub.v:308
/-- Substitution for free type variables in types. -/
def subst_tt (Z : String) (U : typ) (T : typ) : typ :=
  match T with
  | typ.typ_top         => typ.typ_top
  | typ.typ_bvar J      => typ.typ_bvar J
  | typ.typ_fvar X      => if X = Z then U else (typ.typ_fvar X)
  | typ.typ_arrow T1 T2 => typ.typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ.typ_all T1 T2   => typ.typ_all (subst_tt Z U T1) (subst_tt Z U T2)

-- From Fsub.v:319
/-- Substitution for free type variables in terms. -/
def subst_te (Z : String) (U : typ) (e : trm) : trm :=
  match e with
  | trm.trm_bvar i    => trm.trm_bvar i
  | trm.trm_fvar x    => trm.trm_fvar x
  | trm.trm_abs V e1  => trm.trm_abs  (subst_tt Z U V)  (subst_te Z U e1)
  | trm.trm_app e1 e2 => trm.trm_app  (subst_te Z U e1) (subst_te Z U e2)
  | trm.trm_tabs V e1 => trm.trm_tabs (subst_tt Z U V)  (subst_te Z U e1)
  | trm.trm_tapp e1 V => trm.trm_tapp (subst_te Z U e1) (subst_tt Z U V)

-- From Fsub.v:331
/-- Substitution for free term variables in terms. -/
def subst_ee (z : String) (u : trm) (e : trm) : trm :=
  match e with
  | trm.trm_bvar i    => trm.trm_bvar i
  | trm.trm_fvar x    => if x = z then u else (trm.trm_fvar x)
  | trm.trm_abs V e1  => trm.trm_abs V (subst_ee z u e1)
  | trm.trm_app e1 e2 => trm.trm_app (subst_ee z u e1) (subst_ee z u e2)
  | trm.trm_tabs V e1 => trm.trm_tabs V (subst_ee z u e1)
  | trm.trm_tapp e1 V => trm.trm_tapp (subst_ee z u e1) V

-- From Fsub.v:343
/-- Substitution for free type variables in environment bindings. -/
def subst_tb (Z : String) (P : typ) (b : bind) : bind :=
  match b with
  | bind.bind_sub T => bind.bind_sub (subst_tt Z P T)
  | bind.bind_typ T => bind.bind_typ (subst_tt Z P T)
