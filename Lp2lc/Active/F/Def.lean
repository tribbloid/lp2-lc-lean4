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

inductive Bind: Type where
  | stlc: STLC.Bind -> Bind
