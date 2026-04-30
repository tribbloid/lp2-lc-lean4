import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util

namespace Lp2lc.Active

namespace DTLC
/-
dependently typed lambda calculus (similar to STLC but function output type can depend on input term) with a top/wildcard type.
-/

open Util

def Index := Type

section Syntax

variable (I : Index) -- index

mutual

inductive Typ : Type where
| primitive
| depFn (tIn : Typ) (tOut : (arg : I) -> Typ)
| top -- type of anything, can bind both primitive and depFn.

inductive Trm : Type where
| var (symbol : I)
| val (v : Val)
| depApply (fn : Trm) (arg : Trm)

inductive Val : Type where
| primitive (repr : ByteCode)
| depFn (body : (arg : I) -> Trm)
end


def SemTyp := Trm I -> Prop

end Syntax

abbrev TrmClosed := {I : Type} -> Trm I

abbrev TypClosed := {I : Type} -> Typ I

abbrev ValClosed := {I : Type} -> Val I

abbrev PairClosed := {I : Type} -> ((Trm I) × (Val I))

mutual

def Typ.squash : Typ (Trm rep) → Typ rep
 | Typ.primitive => Typ.primitive
 | Typ.depFn tIn tOut =>
    Typ.depFn (Typ.squash tIn) (fun arg => Typ.squash (tOut (Trm.var arg)))
 | Typ.top => Typ.top

def Trm.squash : Trm (Trm rep) → Trm rep
 | Trm.var e => e
 | Trm.val v => Trm.val (Val.squash v)
 | Trm.depApply f a => Trm.depApply (Trm.squash f) (Trm.squash a)

def Val.squash : Val (Trm rep) → Val rep
 | Val.primitive repr => Val.primitive repr
 | Val.depFn body =>
    Val.depFn (fun arg => Trm.squash (body (Trm.var arg)))

end

/--
runtime value, type erased, intermediate representation of "Val" embedded in Lean and executable by Lean. e.g.

- Val.primitive becomes ByteCode directly
- Val.depFn becomes a Lean function `{Arg: Type} -> (arg: Arg) -> (fuel: Nat) -> Option RuntimeVal`

as usual, recursion must be guarded by fuel

it is only for execution, not inspection or verification.
-/
structure SemVal where
  T: Type
  repr: T

/-- recursion must be guarded by fuel -/
def ValClosed.eval (self: ValClosed) : SemVal :=
  sorry
  -- match self (I := SemVal) with
  -- | Val.primitive repr => {T := ByteCode, repr := repr}
  -- | Val.depFn body =>

  --   {T := {I : Type} -> (arg : I) -> (fuel: Nat) -> Option SemVal, repr := body}

namespace Definitional

structure Interpretable where
  term: TrmClosed
  fuel: Nat

/-- Fuel-guarded compile-time type checking for closed terms. True if type-check is successful -/
def Interpretable.typing (self : Interpretable) (typ : TypClosed) : Prop :=
  sorry

/-- Fuel-guarded runtime evaluation for closed terms. some if successful, none if failed -/
def Interpretable.eval (self : Interpretable) : Option SemVal :=
  sorry

end Definitional

-- namespace Runtime

-- inductive Val : Type 1 where -- compiled to be executed/invoked directly in lean, "none" result means failed execution, type is always erased
-- | primitive (v : ByteCode) : Val
-- | fn (body : {T : Type} -> (vIn: T) -> (fuel: Nat) -> Option Val) : Val

-- class Executable (T: Type) where -- with fuel based execution, "none" result means failed execution
--   eval (v : T) (fuel: Nat) : Option Val
--   isAdequet: Prop -- adequecy lemma: given enough fuel, the execution result matches the big-step semantics.

-- -- TODO: define an instance of Executable here

-- end Runtime

-- TODO: define a compilation function here, transforming pair of `Trm : Typ` in syntax into a runtime executable

end DTLC

end Lp2lc.Active
