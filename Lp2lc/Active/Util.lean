

import «Lp2lc».Active.Shared

namespace Lp2lc.Active.Util

abbrev TPayload := Type
abbrev TIndex := Type
abbrev TData := Type

class Free : Type 1 where
  Index : TIndex
  Data : TData

/--
single-use permission to save v into FBound. The permission is for v only and won't work for other value

in runtime, permission to eval is granted for all values

in compiletime, no permission will be granted, you can only save Typ into FBound.

in the future we may:
- let transparent inline function carrying their own permission, so they can eval in compiletime and interact with typing
- add permission to load value From FBound
-/
def Permission (T : Type) := (v: T) -> Prop -- no instance will be provided ever, they are requiremennts to apply AST rules.

namespace Permission

def WideOpen {T} : Permission T := fun _ => true

end Permission

/--
Hypothetical bridge between values & UUIDs as HOAS carrier

There is no way to generate a UUID except saving a `V`, as a result, loading ALWAYS succeed.
As a result, explicit variable substitution (common in de Bruijn serial & named variable stynax) and fuel tower (common in PHOAS) can both be avoided

The UUId can be a dependent type of P, if unnecessary, use FBound alias instead
-/
class DepFBound {P : TPayload} (UUID : P -> TIndex) (V : P -> Type): Type where
  save : (value : V p) → UUID p -- this is the only way to get an UUID (required by HOAS binder): by submitting a `V`. As a result, "load" can be total without introducing free variable
  load : (id : UUID p) → V p
  roundtrip : ∀ (value : V p), load (save value) = value

abbrev FBound (UUID : TIndex) (V : Type) : Type := DepFBound (fun (_ : Unit) => UUID) (fun _ => V)

attribute [simp] DepFBound.roundtrip

section variable {T : Sort u}

/-- Fuel-guarded semantic result used by executable interpreters and compilers. -/
inductive Outcome (T : Sort u)
| yield (v: T)
| outOfFuel

namespace Outcome
variable (self : Outcome T)

def map {T2 : Sort v} (f : T -> T2) : Outcome T2 :=
  match self with
  | .yield v => .yield (f v)
  | .outOfFuel => .outOfFuel

def getOrElse (fallback : T) : T :=
  match self with
  | .yield v => v
  | .outOfFuel => fallback

section variable (T : Type u)

def isResult (self : @Outcome (Option T)) : Prop := match self with
| .yield (some _) => true
| _ => false

def isResultOrOutOfFuel (self : @Outcome (Option T)) : Prop := match self with
| .yield none => false
| _ => true

end
end Outcome

-- universe u v
def Rec (T : Sort u) := (fuel : Nat) -> @Outcome T

abbrev RecOption (T : Type u) := (fuel : Nat) -> @Outcome (Option T)

namespace RecOption
section variable {T : Type u} (self : Lp2lc.Active.Util.RecOption T)

def _shouldYields (expectedV : T) : Prop :=
  ∃ (fuel : Nat), match (self fuel) with
  | .yield (some v) => v = expectedV
  | _ => false

def shouldYields (expectedV : T) : Prop :=
  let hasFuel := _shouldYields self expectedV
  let noFuel := self 0 = .outOfFuel
  hasFuel /\ noFuel

def shouldFail : Prop :=
  let hasFuel := ∃ (fuel : Nat), match (self fuel) with
  | .yield none => true
  | _ => false
  let noFuel := self 0 = .outOfFuel
  hasFuel /\ noFuel

def isDecidable : Prop :=
  ∃ (fuel : Nat), match (self fuel) with
  | .yield (some _) => true
  | _ => false

def isSemiDecidable : Prop :=
  ∀ (fuel : Nat), match (self fuel) with
  | .yield none => false
  | _ => true

end
end RecOption

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
