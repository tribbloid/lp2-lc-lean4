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

structure Carrier where

def TrmClosed.eval(trm: TrmClosed)(typ: TypClosed): ValClosed :=
  sorry

end DTLC

end Lp2lc.Active
