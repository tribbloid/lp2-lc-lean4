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

instance val2trm : Coe (Val I) (Trm I) where
  coe := fun v => Trm.val v

end Syntax

abbrev TypClosed := {I : Index} -> Typ I

abbrev TrmClosed := {I : Index} -> Trm I

abbrev ValClosed := {I : Index} -> Val I

/-- Semantic carrier whose variables are source terms during closed NbE. -/
abbrev SemanticCarrier : Type 1 := Trm PUnit

/-- Evaluation result with normalized output and actual fuel consumed. -/
structure EvalResult (I : Index) where
  output: Option (Val I)
  fuelConsumed: Nat

def EvalResult_Semantic := EvalResult SemanticCarrier

instance astCanReify {AST: Index -> Type} {I : Index} : Coe ({I : Index} -> AST I) (AST I) where
  coe := (fun c => c (I := I))

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

def Trm.lift : Trm I -> Trm (Val I)
| .val value => .val (.ref value)
| .depApply fn arg => .depApply (lift fn) (lift arg)

/-- Normalizes source syntax already instantiated at the semantic carrier. -/
def Trm.evalOpen (term : Trm (Val I)) : (fuel : Nat) -> EvalResult (Val I)
| 0 => { output := none, fuelConsumed := 0 }
| fuel + 1 =>
  match term with
  | .val (.ref (.depFn body)) => { output := some (.depFn (body := (fun
      | .ref value => lift (body value)
      | arg => .val (.ref arg)))), fuelConsumed := 1 }
  | .val value => { output := some value, fuelConsumed := 1 }
  | .depApply fn arg =>
    let fn? := fn.evalOpen fuel; match fn?.output with
    | some (.depFn body) =>
      let arg? := arg.evalOpen fuel; match arg?.output.map (fun value => (body value.squash).evalOpen fuel) with
      | some result =>
        { output := result.output, fuelConsumed := fn?.fuelConsumed + arg?.fuelConsumed + result.fuelConsumed + 1 }
      | none => { output := none, fuelConsumed := fn?.fuelConsumed + arg?.fuelConsumed + 1 }
    | _ => { output := none, fuelConsumed := fn?.fuelConsumed + 1 }

/-- Normalizes a closed term into a closed source value, reporting actual fuel consumed. -/
def TrmClosed.eval (self : TrmClosed) (fuel : Nat) : EvalResult_Semantic :=
  let result := (self (I := Val SemanticCarrier)).evalOpen fuel
  { output := result.output.map Val.squash, fuelConsumed := result.fuelConsumed }

def Trm.pretty (trm : Trm String) : (fuel : Nat) -> String
| 0 => "[out of fuel]"
| fuel + 1 => match trm with
  | Trm.val (.ref s)     => s.down
  | Trm.val (.primitive repr)   => repr
  | Trm.val (.depFn body)   =>
      let x := s!"x_{fuel}"
      s!"(fun {x} => {pretty (body x) (fuel)})"
  | Trm.depApply f a   => s!"({pretty f fuel} {pretty a fuel})"

end DTLC

end Lp2lc.Active
