import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util

namespace Lp2lc.Active

namespace DTLC
/-
dependently typed lambda calculus (similar to STLC but function output type can depend on input term) with a top/wildcard type.
-/

open Util

section Syntax

variable (I : Type) -- index

mutual

inductive Typ : Type where
| primitive : Typ
| depFn (tIn : Typ) (tOut : (arg : I) -> Typ) : Typ
| top: Typ -- type of anything, can bind both primitive and depFn.

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

namespace Runtime

inductive Val : Type 1 where -- compiled to be executed/invoked directly in lean, "none" result means failed execution, type is always erased
| primitive (v : ByteCode) : Val
| fn (body : {T : Type} -> (vIn: T) -> Option Val) : Val

class Executable (T: Type) where -- with fuel based execution, "none" result means failed execution
  eval (v : T) (fuel: Nat) : Option Val
  isAdequet: Prop -- adequecy lemma: given enough fuel, the execution result matches the big-step semantics.

-- TODO: define an instance of Executable here

end Runtime

-- TODO: define a compilation function here, transforming pair of `Trm : Typ` in syntax into a runtime executable

end DTLC

end Lp2lc.Active
