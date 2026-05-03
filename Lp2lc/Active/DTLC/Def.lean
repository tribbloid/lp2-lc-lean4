import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util

namespace Lp2lc.Active

namespace DTLC
/-
dependently typed lambda calculus (similar to STLC but function output type can depend on input term) with a top/wildcard type.
-/

universe u v

-- 1. Implicitly lift a type to a higher universe using ULift
/-- Coerce a lower-universe type into a higher universe through `ULift`. -/
instance _autoUliftType : Coe (Type u) (Type (max u v)) where
  coe := ULift

-- 2. Implicitly lift the values of that type into the ULift wrapper, these 2 enabled universe cumulativity in rocq
/-- Coerce a value into the `ULift` carrier chosen by the lifted type. -/
instance _autoUliftValue {α : Type u} : Coe α (ULift.{v, u} α) where
  coe := ULift.up

structure K : Type

abbrev K1: Type 1 := K

open Util

/-- Universe-1 carrier for PHOAS indices. -/
abbrev Index := Type 1


section Syntax

variable (I : Index) -- index

mutual

inductive Typ : Index where
| primitive
| depFn (tIn : Typ) (tOut : (arg : I) -> Typ)
| top -- type of anything, can bind both primitive and depFn.

inductive Trm : Index where
| val (v : Val)
| depApply (fn : Trm) (arg : Trm)

inductive Val : Index where
| var (symbol : I) -- variable is tolerated as an open value, it just can't exist in closed term at top level
| primitive (repr : ByteCode)
| depFn (body : (arg : I) -> Trm)
end

-- def SemTyp := Trm I -> Prop

end Syntax

def Trm.pretty (trm : Trm String) : (fuel : Nat) -> String
| 0 => "[out of fuel]"
| fuel + 1 => match trm with
  | Trm.val (.var s)     => s.down
  | Trm.val (.primitive repr)   => repr
  | Trm.val (.depFn body)   =>
      let x := s!"x_{fuel}"
      s!"(fun {x} => {pretty (body x) (fuel)})"
  | Trm.depApply f a   => s!"({pretty f fuel} {pretty a fuel})"

abbrev TypClosed := {I : Index} -> Typ I

abbrev TrmClosed := {I : Index} -> Trm I

abbrev ValClosed := {I : Index} -> Val I

abbrev PairClosed := {I : Index} -> ((Trm I) × (Val I))

instance astCanReify {AST: Index -> Type} {I : Index} : Coe ({I : Index} -> AST I) (AST I) where
  coe := (fun c => c (I := I))

/- TODO: should be named "flatten"? -/
-- def Typ.squash : Typ (Trm rep) → Typ rep
--  | Typ.primitive => Typ.primitive
--  | Typ.depFn tIn tOut =>
--     Typ.depFn (Typ.squash tIn) (fun arg => Typ.squash (tOut (Trm.var arg)))
--  | Typ.top => Typ.top

mutual

def Trm.squash : Trm (Val I) → Trm I
 | Trm.val v => Trm.val (Val.squash v)
 | Trm.depApply f a => Trm.depApply (Trm.squash f) (Trm.squash a)

def Val.squash : Val (Val I) → Val I
 | Val.var value => value
 | Val.primitive repr => Val.primitive repr
 | Val.depFn body =>
    Val.depFn (fun arg => Trm.squash (body (Val.var arg)))

end

/--
runtime value, type erased, intermediate representation of "Val" embedded in Lean and executable by Lean. e.g.

- Val.primitive becomes ByteCode directly
- Val.depFn becomes a Lean function `{Arg: Type} -> (arg: Arg) -> (fuel: Nat) -> Option RuntimeVal`

as usual, recursion must be guarded by fuel

it is only for execution, not inspection or verification.
-/
structure SemCarrier : Type 1 where

namespace Definitional

structure Interpretable where
  term: TrmClosed
  fuel: Nat

-- /-- Fuel-guarded compile-time type checking for closed terms. True if type-check is successful -/
-- def Interpretable.typing (self : Interpretable) (typ : TypClosed) : Prop :=

-- private def step {I : Index} : Nat → Trm (Trm I) → Option (Trm I)
--   | 0, _ => none
--   | fuel + 1, term =>
--     match term with
--     | .var term => some term
--     | .val value => some (.val value.squash)
--     | .depApply (.val (.primitive _)) _ => none
--     | .depApply (.val (.depFn body)) arg => some (body arg.squash).squash
--     | .depApply fn arg => step fuel fn |>.map (fun fn' => .depApply fn' arg.squash)


-- here, trm can be open, but open variable must be assigned a `Val I` already
private def _evalSubstituted {I : Index} (trm: Trm (Val I)) : (fuel: Nat) → Option (Val I)
| 0 => none
| fuel + 1 => match trm with
  | .val v => v.squash
  | .depApply fn? arg =>
    sorry

/-- Fuel-guarded runtime evaluation for interpretable closed terms. some if successful, none if failed -/
def Interpretable.eval (self : Interpretable) : Option (Val SemCarrier) :=
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
