

import «Lp2lc».Active.Shared

namespace Lp2lc.Active.Util

abbrev TPayload := Type
abbrev TIndex := Type
abbrev TData := Type

-- DO NOT INTRODUCE BEYOND NECESSITY

/--
collection of free type variables, with index type depending on payload

They are deliberately left free to ward off unlawful construction:

- the only way to construct a `DepIndex p` is to save `Value p` into a `DepFBound`
- it is impossible mingle `DepIndex p1` and `DepIndex p2` if p1 & p2 are different in definition: They are different types
- the only way to construct a `Data` is to parse a primitive literal in AST
- if payload is not required, it can be set to `Unit` (see `Free`)
-/
class DepFree : Type 1 where
  Payload : TPayload
  DepIndex : Payload -> TIndex
  Data : TData

class Free : Type 1 extends DepFree where
  Index : TIndex
  Payload := Unit
  DepIndex := fun _ => Index

namespace Free
abbrev Ref (self : Free) := self.Index × self.Index
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

def WideOpen {T} : Permission T := fun _ => true

end Permission

-- TODO: this should be removed, dependent type constraint (of Payload) cannot provide more information to the compiler
-- /--
-- Hypothetical bridge between values & UIDs as HOAS carrier

-- There is no way to generate a UID except saving a `V`, as a result, loading ALWAYS succeed.
-- As a result, explicit variable substitution (common in de Bruijn serial & named variable stynax) and fuel tower (common in PHOAS) can both be avoided

-- The UID can be a dependent type of P, if unnecessary, use FBound alias instead
-- -/
-- class DepFBound {P : TPayload} (UID : P -> TIndex) (V : P -> Type): Type where
--   save : (value : V p) → UID p -- this is the only way to get an UID (required by HOAS binder): by submitting a `V`. As a result, "load" can be total without introducing free variable
--   load : (id : UID p) → V p
--   roundtrip : ∀ (value : V p), load (save value) = value

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

attribute [simp] FBound.roundtrip

section variable (I: TIndex)

/--
Single key, of which multiple FBoundExt can depends on, they share the same `(K : Type)` & correspondence `(UID.key <-> key)`

V can be Unit, this is a common pattern if it is only useful as a base of other FBoundExt
-/
class FBoundBase
  (K: Type) -- key type, in PL reasoning this is always `Trm I`
: Type where
  save (k : K) : I
  -- this is the only way to get an UID (required by HOAS binder): by submitting a `V`. As a result, "load" can be total without introducing free variable
  load (uid : I) : K -- (k : K) should never be exposed
  roundtrip : ∀ (k : K), load (save k) = k
  isomorph : ∀ (k1 k2 : K), (save k1 = save k2) -> (k1 = k2) -- not sure if useful, just leave it here

attribute [simp] FBoundBase.roundtrip

namespace FBoundBase

/--
Depending on an existing FBoundBase to get the first part of the key

multiple FBoundExt can depend on 1 FBoundBase
-/
class FBoundV2
  {I: TIndex} {K1 : Type} (Base: FBoundBase I K1)
  (K2 V : Type)
: Type where
  savePart (i1: I) (k2 : K2) : I × I
  save (k : K1 × K2) (v: V) : I × I :=
    let i1 := (Base.save k.1) -- TODO: not true, to ensure consistency, any save must be chained to dependent FBoundBase
    savePart i1 k.2

class FBoundV3
  {I: TIndex} {K1 : Type} (Base: FBoundBase I K1)
  (V : Type)
: Type where
  doSave (i1: I) (v : V) : Unit

namespace FBoundV3

def save -- implemented function inside class are just a default argument value. Only dot-methods in the companion namespace are final
    {I : TIndex} {K1 V : Type}
    {Base : FBoundBase I K1}
    (self : Base.FBoundV3 V) (k : K1) (v : V) : I :=
  let i1 := (Base.save k)
  let _ := self.doSave i1 v
  i1

end FBoundV3

theorem FBoundV3.saveIso
    {I : TIndex} {K1 _V V V2 : Type}
    {Base : FBoundBase I K1}
    [self : Base.FBoundV3 V]
    [other : Base.FBoundV3 V2]
    (k1 : K1) (v : V) (v2 : V2) :
    self.save (k1) v = other.save (k1) v2 := by
  rfl

end FBoundBase

end

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

def isDecidable (condition: T -> Prop := fun _ => True) : Prop :=
  ∃ (fuel : Nat), match (self fuel) with
  | .yield (some v) => condition v
  | _ => false

def isSemiDecidable (condition: T -> Prop := fun _ => True) : Prop :=
  ∀ (fuel : Nat), match (self fuel) with
  | .yield none => false
  | .outOfFuel => true
  | .yield (some v) => condition v

def shouldYields (expectedV : T) : Prop :=
  let hasFuel := RecOption.isDecidable self (fun v => v = expectedV)
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
