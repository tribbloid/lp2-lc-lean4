
import «Lp2lc».Active.Shared

namespace Lp2lc.Active.Util

abbrev TIndex := Type
abbrev TData := Type

-- DO NOT INTRODUCE BEYOND NECESSITY

inductive Phase
  | compilation
  | runtime

/--
collection of free type variables used in HOAS bindings

They are deliberately left free to ward off unlawful construction:

- the only way to construct an `Index` is to save `Value` into an `FBound`
- the only way to construct a `Data` is to parse a primitive literal in AST
-/
class Free : Type 1 where
  Index : TIndex
  Data : TData

namespace Free
section variable [free : Free]

structure UID (kind : Phase) where
  index : free.Index

@[reducible] def AsIn (kind : Phase) : Free where
  Index := UID kind
  Data := free.Data

end
end Free

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

def WideOpen {T} : Permission T := λ _ => true

end Permission

/--
thin wrapper of `T` representing outcome of a valid compilation, implying safety of associated code snippet.

all compilation API should ideally return this.

if saved in an FBound, the result UID should work in any `Env` to get a compatible term or value.
-/
structure Valid T : Type where
  self: T

/--
Hypothetical bridge between values & UIDs as HOAS carrier

There is no way to generate a UID except saving a `V`, as a result, loading ALWAYS succeed.
As a result, explicit variable substitution (common in de Bruijn serial & named variable stynax) and fuel tower (common in PHOAS) can both be avoided
-/
class FBound (UID : TIndex) (V : Type): Type where
  save : (value : V) → UID -- this is the only way to get an UID (required by HOAS binder): by submitting a `V`. As a result, "load" can be total without introducing free variable
  load : (id : UID) → V
  roundtrip : ∀ (value : V), load (save value) = value
  -- saveTwice (v1 v2 : V): save v1 = save v2
  -- loadTwice (id1 id2 : UID): load id1 = load id2


structure FBoundGroup : Type 1 where
  (UID: TIndex)
  (V: Type)

/--
this is an upgraded FBound which depends on FBoundGroup:

- designed to save/load a value with a `metadata : Type/Prop` that depends on it
- `save` computes UID only from value, metadata is required but not used
- all FBoundV2 instances from the same group share the same isomorphism of UID <-> group.V
- the metadata can be set to Unit type to achieve the original FBound behaviour
-/
class FBoundV2 (G : FBoundGroup) (D: G.V -> (Sort u)) where
  Bundle: (value : G.V) × (metadata: D value)
  save : (bundle : Bundle) → group.UID -- this is the only way to get an UID (required by HOAS binder): by submitting a `V`. As a result, "load" can be total without introducing free variable
  load : (id : group.UID) → Bundle

-- namespace FBoundGroup
-- section variable (group : FBoundGroup)

-- end
-- end FBoundGroup

namespace FBound
end FBound

attribute [simp] FBound.roundtrip

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

def flatMap {T2 : Sort v} (f : T -> Outcome T2) : Outcome T2 :=
  match self with
  | .yield v => f v
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

-- TODO: all algorithm with this signature should have a proof of monotonicity

namespace Rec
section variable (self : Lp2lc.Active.Util.Rec T)

/-- Recursive computations stay successful with more fuel for the same result. -/
def Monotone : Prop :=
  ∀ (less more : Nat) (value : T),
  (less <= more) ->
  self less = .yield value ->
  self more = .yield value

end
end Rec

abbrev RecOption (T : Type u) := Rec (Option T)

namespace RecOption
section variable {T : Type u} (self : Lp2lc.Active.Util.RecOption T)

def isDecidable (condition: T -> Prop := λ _ => True) : Prop :=
  ∃ (fuel : Nat), match (self fuel) with
  | .yield (some v) => condition v
  | _ => false

def isSemiDecidable (condition: T -> Prop := λ _ => True) : Prop :=
  ∀ (fuel : Nat), match (self fuel) with
  | .yield none => false
  | .outOfFuel => true
  | .yield (some v) => condition v

def shouldYields (expectedV : T) : Prop :=
  let hasFuel := RecOption.isDecidable self (λ v => v = expectedV)
  let noFuel := self 0 = .outOfFuel
  hasFuel /\ noFuel

def shouldFail : Prop :=
  let hasFuel := ∃ (fuel : Nat), match (self fuel) with
  | .yield none => true
  | _ => false
  let noFuel := self 0 = .outOfFuel
  hasFuel /\ noFuel

end
end RecOption

end

end Lp2lc.Active.Util

namespace Lp2lc.Active.Util

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
