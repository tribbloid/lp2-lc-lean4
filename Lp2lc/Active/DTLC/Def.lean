import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util

namespace Lp2lc.Active

namespace STLC
/-
dependently typed lambda calculus, STLC but function output type can depend on input term.

Conventions:


-/

open Util

section Syntax

variable (I: Type)[DecidableEq I] -- index

mutual

inductive Typ : Type where
| primitive : Typ
| depFn (tIn : Typ) (tOut: (arg: I) -> Typ) : Typ

inductive Trm : Type where
| var (symbol: I) (tAnnotation: Typ) : Trm
| val (v : Val) : Trm
| depApply (fn: Trm) (arg: Trm) : Trm

inductive Val : Type where
| primitive (repr: ByteCode) : Val
| depFn (body : (arg: I) -> Trm) : Val
end

end Syntax



end STLC

end Lp2lc.Active
