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
| ref (symbol : I) -- Reference to an unkonwn indexed thing. Closed term cannot have it outside depFn body, open value (open term doesn't have such limitation). AKA variable but this name is misleading (lambda calculus doesn't have mutablle binding)
| primitive (repr : ByteCode)
| depFn (body : (arg : I) -> Trm)
end

-- def SemTyp := Trm I -> Prop

end Syntax

def Trm.pretty (trm : Trm String) : (fuel : Nat) -> String
| 0 => "[out of fuel]"
| fuel + 1 => match trm with
  | Trm.val (.ref s)     => s.down
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
| Val.ref value => value
| Val.primitive repr => Val.primitive repr
| Val.depFn body =>
  Val.depFn (fun arg =>
    let argVar := Val.ref arg
    Trm.squash (body argVar)
  )

end

namespace FBound

class FBound (I : Index) where -- fixed-point cast, looks like a reversed Env, it cast `Trm I` into something Val.depFn can accept
  cast: Val I -> I

end FBound

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
-- private def _evalSubstituted {I : Index} (trm: Trm (Val I)) : (fuel: Nat) → Option (Val (Val I))
-- | 0 => none
-- | fuel + 1 => match trm with
--   | .val v => some v
--   | .depApply fn? arg =>
--     let anf := (_evalSubstituted fn? fuel, _evalSubstituted arg fuel) -- atomic normal form
--     match anf with
--     | (some (Val.depFn fnBody), some _arg) =>
--       let applied := (fnBody _arg.squash)
--       let result := _evalSubstituted applied fuel
--       result
--     | _ => none

end Definitional

-- /-- Fuel-guarded runtime evaluation for interpretable closed terms. some if successful, none if failed -/
-- def ClosedTrm.eval (self : ClosedTrm) (fuel : Nat) : Option (Val SemCarrier) :=
--   let almost := Definitional._evalSubstituted (self (I := Val SemCarrier)) fuel
--   almost.map fun v => v.squash


/--
runtime value, type erased, intermediate representation of "Val" embedded in Lean and executable by Lean. e.g.

- Val.primitive becomes ByteCode directly
- Val.depFn becomes a Lean function `{Arg: Type} -> (arg: Arg) -> (fuel: Nat) -> Option RuntimeVal`

as usual, recursion must be guarded by fuel

it is only for execution, not inspection or verification.
-/
abbrev SemanticCarrier : Type 1 := sorry

structure EvalResult where
  output: Option (Val SemanticCarrier)
  fuelConsumed: Nat

/-- Fuel-guarded runtime evaluation for interpretable closed terms. some if successful, none if failed -/
def ClosedTrm.eval (self : TrmClosed) (fuel : Nat) : EvalResult :=
  sorry

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
