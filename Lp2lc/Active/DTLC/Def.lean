import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util

namespace Lp2lc.Active

namespace DTLC
/-
dependently typed lambda calculus, STLC but function output type can depend on input term.
-/

open Util

universe u

section Syntax

variable (I : Sort u) -- index

mutual

inductive Typ : Type (u + 1) where
| primitive : Typ
| depFn (tIn : Typ) (tOut : (arg : I) -> Typ) : Typ

inductive Trm : Type (u + 1) where
| var (symbol : I) {tAnnotation : Typ} : Trm
| val (v : Val) : Trm
| depApply (fn : Trm) (arg : Trm) : Trm

inductive Val : Type (u + 1) where
| primitive (repr : ByteCode) : Val
| depFn (body : (arg : I) -> Trm) : Val
end

end Syntax

abbrev TrmClosed := {I : Sort u} -> Trm I

abbrev TypClosed := {I : Sort u} -> Typ I

structure RuntimeCarrier where
  self: ByteCode

abbrev RuntimeVal := Val RuntimeCarrier

namespace TrmClosed

@[simp]
def eval (trm : TrmClosed) (fuel : Nat) : Option RuntimeVal := sorry

-- @[simp]
-- def typing (trm : TrmClosed) (fuel : Nat) (typ : TypClosed) : Prop := sorry

end TrmClosed

end DTLC

end Lp2lc.Active
