

import «Lp2lc».Active.Shared

namespace Lp2lc.Active.Util

abbrev KIndex := Type
abbrev KData := Type

class Impl : Type 1 where
  Index : KIndex
  Data : KData

/--
single-use permission to save v into FBound. The permission is for v only and won't work for other value

in runtime, permission to eval is granted for all values

in compiletime, no permission will be granted, you can only save Typ into FBound.

in the future we may:
- let transparent inline function carrying their own permission, so they can eval in compiletime and interact with typing
- add permission to load value From FBound
-/
def Permission (T : Type) := (v: T) -> Prop -- no instance will be provided ever, they are requiremennts to apply AST rules.

/-- Fixed-bound bridge between a HOAS carrier and the syntax family it represents. -/
class FBound (I : KIndex) (V : Type) (P : Permission V): Type where -- fixed-point bound axiom, a crossover between de-bruijn Env/Store & HOAS carrier.
  save : (value : V) -> (permission: P value) → I -- `I` is unknown & there is no way to get `I` (required by HOAS binder) except submitting a `V`.
  load : (index : I) → V -- inverse of save
  roundtrip : ∀ (value : V), (permission : P value) → load (save value permission) = value

-- class Env (P: Index) (I : Index) (K : (index : Index) → Type) where
--   fBound : FBound I K
--   permission: P

attribute [simp] FBound.roundtrip

section variable {T : Sort u}

/-- Fuel-guarded semantic result used by executable interpreters and compilers. -/
inductive Outcome
| result (v: T)
| error
| outOfFuel

namespace Outcome
section variable (self: @Outcome T)

def isResult : Prop := match self with
| result _ => true
| _ => false

def isResultOrOutOfFuel : Prop := match self with
| error  => false
| _ => true

end
end Outcome

-- universe u v

def MayTerminate (T : Sort u) := (fuel: Nat) -> @Outcome T

namespace MayTerminate
section variable  (self : @MayTerminate T)

def shouldYieldsWithFuel (expectedV: T) : Prop :=
  ∃ (fuel : Nat), match (self fuel) with
  | .result v => v = expectedV
  | _ => false

def shouldYields  (expectedV: T) : Prop :=
  let hasFuel := self.shouldYieldsWithFuel expectedV
  let noFuel := self 0 = .outOfFuel
  hasFuel /\ noFuel

def shouldFail  : Prop :=
  let hasFuel := ∃ (fuel : Nat), match (self fuel) with
  | .error => true
  | _ => false
  let noFuel := self 0 = .outOfFuel
  hasFuel /\ noFuel

def isDecidable  : Prop :=
  ∃ (fuel : Nat), match (self fuel) with
  | .result _ => true
  | _ => false

def isSemiDecidable  : Prop :=
  ∀ (fuel: Nat), match (self fuel) with
  | .error  => false
  | _ => true

end
end MayTerminate

def MaySucceed (T : Type) := (fuel : Nat) -> {x : @Outcome T // x.isResultOrOutOfFuel}

end

def IProp := Prop

-- 1. Implicitly lift a type to a higher universe using ULift
/-- Coerce a lower-universe type into a higher universe through `ULift`. -/
instance _autoUliftType : Coe (Type u) (Type (max u v)) where
  coe := ULift

-- 2. Implicitly lift the values of that type into the ULift wrapper, these 2 enabled universe cumulativity in rocq
/-- Coerce a value into the `ULift` carrier chosen by the lifted type. -/
instance _autoUliftValue {α : Type u} : Coe α (ULift.{v, u} α) where
  coe := ULift.up
abbrev Name := String

end Util
