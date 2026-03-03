import Mathlib.Tactic
import «Lp2lc».Active.Shared
import «Lp2lc».Active.STLC

namespace Lp2lc.Active.F

inductive Typ : Type where
  | stlc : STLC.Typ -> Typ
  | bvar : Nat -> Typ
  | fvar : Var -> Typ
deriving DecidableEq, Repr

inductive Trm : Type where
  | stlc: STLC.Trm -> Trm
  | tabs : Trm -> Trm
  | tapp : Trm -> Typ -> Trm
deriving DecidableEq, Repr

namespace Ops

@[simp]
def subst_fvar {a : Type} (mk : Var -> a) (x : Var) (u : a) (y : Var) : a :=
  if y = x then u else mk y

@[simp]
def open_bvar {a : Type} (mk : Nat -> a) (k i : Nat) (u : a) : a :=
  if k = i then u else mk i

@[simp]
def close_fvar {a : Type} (mk_bvar : Nat -> a) (mk_fvar : Var -> a) (k : Nat) (x y : Var) : a :=
  if x = y then mk_bvar k else mk_fvar y

end Ops
