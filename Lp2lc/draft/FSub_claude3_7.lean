import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic

open Set

/-- Variable type for both term and type variables -/
def var := String

instance : Repr var := inferInstanceAs (Repr String)
instance : BEq var := inferInstanceAs (BEq String)
instance : DecidableEq var := inferInstanceAs (DecidableEq String)

/-- Representation of pre-types -/
inductive typ : Type where
  | typ_top : typ
  | typ_bvar : Nat → typ
  | typ_fvar : var → typ
  | typ_arrow : typ → typ → typ
  | typ_all : typ → typ → typ
deriving Repr, BEq, DecidableEq

/-- Representation of pre-terms -/
inductive trm : Type where
  | trm_bvar : Nat → trm
  | trm_fvar : var → trm
  | trm_abs : typ → trm → trm
  | trm_app : trm → trm → trm
  | trm_tabs : typ → trm → trm
  | trm_tapp : trm → typ → trm
deriving Repr, BEq, DecidableEq

/-- Opening up a type binder occurring in a type -/
def open_tt_rec : Nat → typ → typ → typ
  | _, _, typ.typ_top => typ.typ_top
  | K, U, typ.typ_bvar J => if K = J then U else typ.typ_bvar J
  | _, _, typ.typ_fvar X => typ.typ_fvar X
  | K, U, typ.typ_arrow T1 T2 => typ.typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | K, U, typ.typ_all T1 T2 => typ.typ_all (open_tt_rec K U T1) (open_tt_rec (K+1) U T2)

/-- Opening up a type with another type at index 0 -/
def open_tt (T U : typ) : typ := open_tt_rec 0 U T

/-- Opening up a type binder occurring in a term -/
def open_te_rec : Nat → typ → trm → trm
  | _, _, trm.trm_bvar i => trm.trm_bvar i
  | _, _, trm.trm_fvar x => trm.trm_fvar x
  | K, U, trm.trm_abs V e1 => trm.trm_abs (open_tt_rec K U V) (open_te_rec K U e1)
  | K, U, trm.trm_app e1 e2 => trm.trm_app (open_te_rec K U e1) (open_te_rec K U e2)
  | K, U, trm.trm_tabs V e1 => trm.trm_tabs (open_tt_rec K U V) (open_te_rec (K+1) U e1)
  | K, U, trm.trm_tapp e1 V => trm.trm_tapp (open_te_rec K U e1) (open_tt_rec K U V)

/-- Opening up a term with a type at index 0 -/
def open_te (t : trm) (U : typ) : trm := open_te_rec 0 U t

/-- Opening up a term binder occurring in a term -/
def open_ee_rec : Nat → trm → trm → trm
  | k, f, trm.trm_bvar i => if k = i then f else trm.trm_bvar i
  | _, _, trm.trm_fvar x => trm.trm_fvar x
  | k, f, trm.trm_abs V e1 => trm.trm_abs V (open_ee_rec (k+1) f e1)
  | k, f, trm.trm_app e1 e2 => trm.trm_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | k, f, trm.trm_tabs V e1 => trm.trm_tabs V (open_ee_rec k f e1)
  | k, f, trm.trm_tapp e1 V => trm.trm_tapp (open_ee_rec k f e1) V

/-- Opening up a term with another term at index 0 -/
def open_ee (t u : trm) : trm := open_ee_rec 0 u t

/-- Notation for opening up binders with type or term variables -/
def open_tt_var (T : typ) (X : var) : typ := open_tt T (typ.typ_fvar X)
def open_te_var (t : trm) (X : var) : trm := open_te t (typ.typ_fvar X)
def open_ee_var (t : trm) (x : var) : trm := open_ee t (trm.trm_fvar x)

/-- Types as locally closed pre-types -/
inductive type : typ → Prop where
  | type_top : 
      type typ.typ_top
  | type_var : ∀ X,
      type (typ.typ_fvar X)
  | type_arrow : ∀ T1 T2,
      type T1 →
      type T2 →
      type (typ.typ_arrow T1 T2)
  | type_all : ∀ (L : Set var) (T1 T2 : typ),
      type T1 →
      (∀ X, X ∉ L → type (open_tt_var T2 X)) →
      type (typ.typ_all T1 T2)

/-- Terms as locally closed pre-terms -/
inductive term : trm → Prop where
  | term_var : ∀ x,
      term (trm.trm_fvar x)
  | term_abs : ∀ (L : Set var) (V : typ) (e1 : trm),
      type V →
      (∀ x, x ∉ L → term (open_ee_var e1 x)) →
      term (trm.trm_abs V e1)
  | term_app : ∀ e1 e2,
      term e1 →
      term e2 →
      term (trm.trm_app e1 e2)
  | term_tabs : ∀ (L : Set var) (V : typ) (e1 : trm),
      type V →
      (∀ X, X ∉ L → term (open_te_var e1 X)) →
      term (trm.trm_tabs V e1)
  | term_tapp : ∀ e1 V,
      term e1 →
      type V →
      term (trm.trm_tapp e1 V)

/-- Bindings are either mapping type or term variables.
    [X ~<: T] is a subtyping assumption and [x ~: T] is a typing assumption -/
inductive bind : Type where
  | bind_sub : typ → bind
  | bind_typ : typ → bind
deriving Repr, BEq

/-- Environment is a list of bindings -/
def env := List (var × bind)

/-- Empty environment -/
def empty : env := []

/-- Add a binding to an environment -/
def add (E : env) (b : var × bind) : env := b :: E

/-- Notation for adding a binding to an environment -/
notation E " & " b => add E b

/-- Check if a variable is bound in an environment -/
def dom (E : env) : List var := E.map Prod.fst

/-- Check if a variable is fresh in an environment -/
def fresh (x : var) (E : env) : Prop := ¬List.elem x (dom E)

/-- Notation for freshness -/
notation x " # " E => fresh x E

/-- Find the binding of a variable in an environment -/
def binds (x : var) (b : bind) (E : env) : Prop := List.elem (x, b) E

/-- Well-formedness of a pre-type T in an environment E -/
inductive wft : env → typ → Prop
  | wft_top : ∀ (E : env),
      wft E typ.typ_top
  | wft_var : ∀ (U : typ) (E : env) (X : var),
      binds X (bind.bind_sub U) E →
      wft E (typ.typ_fvar X)
  | wft_arrow : ∀ (E : env) (T1 T2 : typ),
      wft E T1 →
      wft E T2 →
      wft E (typ.typ_arrow T1 T2)
  | wft_all : ∀ (L : Set var) (E : env) (T1 T2 : typ),
      wft E T1 →
      (∀ (X : var), X ∉ L →
        wft (E & (X, bind.bind_sub T1)) (open_tt_var T2 X)) →
      wft E (typ.typ_all T1 T2)

/-- A environment E is well-formed -/
inductive okt : env → Prop
  | okt_empty :
      okt empty
  | okt_sub : ∀ (E : env) (X : var) (T : typ),
      okt E → wft E T → X # E → okt (E & (X, bind.bind_sub T))
  | okt_typ : ∀ (E : env) (x : var) (T : typ),
      okt E → wft E T → x # E → okt (E & (x, bind.bind_typ T))

/-- Subtyping relation -/
inductive sub : env → typ → typ → Prop
  | sub_top : ∀ (E : env) (S : typ),
      okt E →
      wft E S →
      sub E S typ.typ_top
  | sub_refl_tvar : ∀ (E : env) (X : var),
      okt E →
      wft E (typ.typ_fvar X) →
      sub E (typ.typ_fvar X) (typ.typ_fvar X)
  | sub_trans_tvar : ∀ (U : typ) (E : env) (T : typ) (X : var),
      binds X (bind.bind_sub U) E →
      sub E U T →
      sub E (typ.typ_fvar X) T
  | sub_arrow : ∀ (E : env) (S1 S2 T1 T2 : typ),
      sub E T1 S1 →
      sub E S2 T2 →
      sub E (typ.typ_arrow S1 S2) (typ.typ_arrow T1 T2)
  | sub_all : ∀ (L : Set var) (E : env) (S1 S2 T1 T2 : typ),
      sub E T1 S1 →
      (∀ (X : var), X ∉ L →
          sub (E & (X, bind.bind_sub T1)) (open_tt_var S2 X) (open_tt_var T2 X)) →
      sub E (typ.typ_all S1 S2) (typ.typ_all T1 T2)

/-- Typing relation -/
inductive typing : env → trm → typ → Prop
  | typing_var : ∀ (E : env) (x : var) (T : typ),
      okt E →
      binds x (bind.bind_typ T) E →
      typing E (trm.trm_fvar x) T
  | typing_abs : ∀ (L : Set var) (E : env) (V : typ) (e1 : trm) (T1 : typ),
      (∀ (x : var), x ∉ L →
        typing (E & (x, bind.bind_typ V)) (open_ee_var e1 x) T1) →
      okt E →
      wft E V →
      wft E T1 →
      typing E (trm.trm_abs V e1) (typ.typ_arrow V T1)
  | typing_app : ∀ (E : env) (e1 e2 : trm) (T1 T2 : typ),
      typing E e1 (typ.typ_arrow T1 T2) →
      typing E e2 T1 →
      typing E (trm.trm_app e1 e2) T2
  | typing_tabs : ∀ (L : Set var) (E : env) (V : typ) (e1 : trm) (T1 : typ),
      (∀ (X : var), X ∉ L →
        typing (E & (X, bind.bind_sub V)) (open_te_var e1 X) (open_tt_var T1 X)) →
      okt E →
      wft E V →
      typing E (trm.trm_tabs V e1) (typ.typ_all V T1)
  | typing_tapp : ∀ (E : env) (e1 : trm) (T1 T2 T : typ),
      typing E e1 (typ.typ_all T1 T2) →
      sub E T T1 →
      typing E (trm.trm_tapp e1 T) (open_tt T2 T)
  | typing_sub : ∀ (E : env) (e : trm) (T1 T2 : typ),
      typing E e T1 →
      sub E T1 T2 →
      wft E T2 →
      typing E e T2

/-- Values -/
inductive value : trm → Prop where
  | value_abs : ∀ (V : typ) (e1 : trm), 
      term (trm.trm_abs V e1) →
      value (trm.trm_abs V e1)
  | value_tabs : ∀ (V : typ) (e1 : trm), 
      term (trm.trm_tabs V e1) →
      value (trm.trm_tabs V e1)

/-- One-step reduction -/
inductive red : trm → trm → Prop where
  | red_app_1 : ∀ (e1 e1' e2 : trm),
      term e2 →
      red e1 e1' →
      red (trm.trm_app e1 e2) (trm.trm_app e1' e2)
  | red_app_2 : ∀ (e1 e2 e2' : trm),
      value e1 →
      red e2 e2' →
      red (trm.trm_app e1 e2) (trm.trm_app e1 e2')
  | red_tapp : ∀ (e1 e1' : trm) (V : typ),
      type V →
      red e1 e1' →
      red (trm.trm_tapp e1 V) (trm.trm_tapp e1' V)
  | red_abs : ∀ (V : typ) (e1 v2 : trm),
      term (trm.trm_abs V e1) →
      value v2 →
      red (trm.trm_app (trm.trm_abs V e1) v2) (open_ee e1 v2)
  | red_tabs : ∀ (V1 : typ) (e1 : trm) (V2 : typ),
      term (trm.trm_tabs V1 e1) →
      type V2 →
      red (trm.trm_tapp (trm.trm_tabs V1 e1) V2) (open_te e1 V2)

/-- Preservation statement -/
def preservation : Prop := ∀ (E : env) (e e' : trm) (T : typ),
  typing E e T →
  red e e' →
  typing E e' T

/-- Progress statement -/
def progress : Prop := ∀ (e : trm) (T : typ),
  typing empty e T →
  value e ∨ ∃ e', red e e'
