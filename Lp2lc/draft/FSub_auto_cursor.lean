import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic

import Aesop

-- System Fsub: Syntax (from Rocq Fsub.v)

-- We use Nat for de Bruijn indices and String for variable names (could be changed to a custom type if needed)

def var : Type := String deriving DecidableEq, Repr

inductive typ : Type
| top : typ
| bvar : Nat → typ
| fvar : var → typ
| arrow : typ → typ → typ
| all : typ → typ → typ
  deriving DecidableEq, Repr

inductive trm : Type
| bvar : Nat → trm
| fvar : var → trm
| abs  : typ → trm → trm
| app  : trm → trm → trm
| tabs : typ → trm → trm
| tapp : trm → typ → trm
  deriving DecidableEq, Repr

-- Opening up a type binder occurring in a type
partial def open_tt_rec (K : Nat) (U : typ) : typ → typ
| typ.top         => typ.top
| typ.bvar J      => if K = J then U else typ.bvar J
| typ.fvar X      => typ.fvar X
| typ.arrow T1 T2 => typ.arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
| typ.all T1 T2   => typ.all (open_tt_rec K U T1) (open_tt_rec (K+1) U T2)

def open_tt (T U : typ) : typ := open_tt_rec 0 U T

-- Opening up a type binder occurring in a term
partial def open_te_rec (K : Nat) (U : typ) : trm → trm
| trm.bvar i      => trm.bvar i
| trm.fvar x      => trm.fvar x
| trm.abs V e1    => trm.abs (open_tt_rec K U V) (open_te_rec K U e1)
| trm.app e1 e2   => trm.app (open_te_rec K U e1) (open_te_rec K U e2)
| trm.tabs V e1   => trm.tabs (open_tt_rec K U V) (open_te_rec (K+1) U e1)
| trm.tapp e1 V   => trm.tapp (open_te_rec K U e1) (open_tt_rec K U V)

def open_te (t : trm) (U : typ) : trm := open_te_rec 0 U t

-- Opening up a term binder occurring in a term
partial def open_ee_rec (k : Nat) (f : trm) : trm → trm
| trm.bvar i      => if k = i then f else trm.bvar i
| trm.fvar x      => trm.fvar x
| trm.abs V e1    => trm.abs V (open_ee_rec (k+1) f e1)
| trm.app e1 e2   => trm.app (open_ee_rec k f e1) (open_ee_rec k f e2)
| trm.tabs V e1   => trm.tabs V (open_ee_rec k f e1)
| trm.tapp e1 V   => trm.tapp (open_ee_rec k f e1) V

def open_ee (t u : trm) : trm := open_ee_rec 0 u t

-- Notation for opening up binders with type or term variables
notation:67 T "open_tt_var" X => open_tt T (typ.fvar X)
notation:67 t "open_te_var" X => open_te t (typ.fvar X)
notation:67 t "open_ee_var" x => open_ee t (trm.fvar x)

-- Bindings are either mapping type or term variables
inductive bind : Type
| sub : typ → bind
| typ : typ → bind
  deriving DecidableEq, Repr

-- Environment is a list of bindings
abbrev env := List (var × bind)

def empty : env := []

def add (E : env) (b : var × bind) : env := b :: E
notation E " & " b => add E b

def dom (E : env) : List var := E.map Prod.fst

def fresh (x : var) (E : env) : Prop := ¬List.elem x (dom E)
notation x " # " E => fresh x E

def binds (x : var) (b : bind) (E : env) : Prop := List.elem (x, b) E

-- Notation for subtyping and typing bindings
notation X " ~<: " T => (X, bind.sub T)
notation x " ~: " T => (x, bind.typ T)

-- Well-formed types (locally closed types)
inductive type : typ → Prop where
| top : type typ.top
| var : ∀ X, type (typ.fvar X)
| arrow : ∀ T1 T2, type T1 → type T2 → type (typ.arrow T1 T2)
| all : ∀ (L : Set var) (T1 T2 : typ),
    type T1 → (∀ X, X ∉ L → type (T2 open_tt_var X)) → type (typ.all T1 T2)

deriving Repr

-- Well-formed terms (locally closed terms)
inductive term : trm → Prop where
| var : ∀ x, term (trm.fvar x)
| abs : ∀ (L : Set var) (V : typ) (e1 : trm),
    type V → (∀ x, x ∉ L → term (e1 open_ee_var x)) → term (trm.abs V e1)
| app : ∀ e1 e2, term e1 → term e2 → term (trm.app e1 e2)
| tabs : ∀ (L : Set var) (V : typ) (e1 : trm),
    type V → (∀ X, X ∉ L → term (e1 open_te_var X)) → term (trm.tabs V e1)
| tapp : ∀ e1 V, term e1 → type V → term (trm.tapp e1 V)

deriving Repr
