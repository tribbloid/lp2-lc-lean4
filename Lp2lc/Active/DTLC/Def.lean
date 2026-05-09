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
abbrev Index := Type

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
| primitive (repr : ByteCode)
| fn (body : (arg : I) -> Trm)

end

instance valIsTrm : Coe (Val I) (Trm I) where
  coe := (fun v => Trm.val v)

end Syntax

class FBound (I : Index) where -- fixed-point cast, looks like a reversed Env, it cast `Trm I` into something Val.depFn can accept
  fwd: Val I -> I -- useful in eval, definition uses the inverse but interpreter is not allowed to see it.

inductive Outcome (T : Index)
| some (v: T)
| error
| outOfFuel

namespace Outcome

def isSome : (self: Outcome T) -> Prop
| .some _ => true
| _ => false

end Outcome

/-- Normalizes source terms to values while spending fuel at each semantic descent -/
def Trm.eval {I : Index} [FBound I] (trm : Trm I) (fuel : Nat) : Outcome (Val I) :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match trm with
    | .val value => .some value
    | .depApply fn arg =>
      match fn.eval fuel, arg.eval fuel with
      | .some (.fn body), .some value => (body (FBound.fwd value)).eval fuel
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .error

/--
fuel-guarded compiler API that verify a type-annotated term and:

- if semantic type-check succeeds, generate a more specialised, executable term. This execution should always succeed (adequency lemma).
- else if type-check fails, return error
- always return outOfFuel if fuel drops to 0

semantic typing (a predicate on ) is merely this API being successful

this is a critical semantic rule for proving:

- adequecy lemma: a successfully compiled term can always be successfully executed (to
  a value that can be type-checked by the same type) or run out of fuel.
- fundamental lemma: if a type-annotated function and it's compatible argumennt
  can both be successfully compiled, then their applied form can also be
  successfull ccompiled.
- finally, soundness theorem that uses the above 2 lemma
-/
def Trm.compile {I : Index} [FBound I] (trm: Trm I) (fuel: Nat) (typeAnnotation: Typ I): Outcome (Trm I) :=
  sorry

def Trm.typing {I : Index} [FBound I] (typeAnnotation: Typ I) (fuel: Nat)  (trm: Trm I) : Prop :=
  (trm.compile fuel typeAnnotation).isSome



end DTLC

end Lp2lc.Active
