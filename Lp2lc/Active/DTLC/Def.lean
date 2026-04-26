import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util

namespace Lp2lc.Active

namespace DTLC
/-
dependently typed lambda calculus, STLC but function output type can depend on input term.
-/

open Util

section Syntax

variable (I : Type) -- index

mutual

inductive Typ : Type where
| primitive : Typ
| depFn (tIn : Typ) (tOut : (arg : I) -> Typ) : Typ

inductive Trm : Type where
| var (symbol : I) : Trm
| val (v : Val) : Trm
| depApply (fn : Trm) (arg : Trm) : Trm

inductive Val : Type where
| primitive (repr : ByteCode) : Val
| depFn (body : (arg : I) -> Trm) : Val
end

end Syntax

abbrev TrmClosed := {I : Type} -> Trm I

abbrev TypClosed := {I : Type} -> Typ I

abbrev ValClosed := {I : Type} -> Val I

mutual

def Trm.squash : Trm (Trm rep) → Trm rep
 | Trm.var e => e
 | Trm.val v => Trm.val (Val.squash v)
 | Trm.depApply f a => Trm.depApply (Trm.squash f) (Trm.squash a)

def Val.squash : Val (Trm rep) → Val rep
 | Val.primitive repr => Val.primitive repr
 | Val.depFn body => Val.depFn (fun arg => Trm.squash (body (Trm.var arg)))

end

structure Carrier where

def TrmClosed.eval(trm: TrmClosed)(fuel: Nat): Option ValClosed :=
  sorry

end DTLC

end Lp2lc.Active
