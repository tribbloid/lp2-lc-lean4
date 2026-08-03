
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

- the only way to construct an `Index` is to get the UID of a `Value` through the fixpoint bridge
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
single-use permission to get the UID of v from a `UIDEquiv`. The permission is for v only and won't work for other value

in runtime, permission to eval is granted for all values

in compiletime, no permission will be granted, you can only get the UID of a Typ from a `UIDEquiv`.

in the future we may:
- let transparent inline function carrying their own permission, so they can eval in compiletime and interact with typing
- add permission to reconstruct a value from a `UIDEquiv`
-/
def Permission (T : Type) := (v: T) -> Prop -- no instance will be provided ever, they are requiremennts to apply AST rules.

namespace Permission

def WideOpen {T} : Permission T := λ _ => true

end Permission

/--
thin wrapper of `T` representing outcome of a valid compilation, implying safety of associated code snippet.

all compilation API should ideally return this.

if registered in a `UIDEquiv`, the result UID should work in any `Env` to get a compatible term or value.
-/
structure Valid T : Type where
  self: T

/--
Hypothetical bridge between values & UIDs as HOAS carrier

[UIDEquiv.getUID] is the only way to obtain a UID: it requires a `V`.
Consequently, [UIDEquiv.inv] is total without introducing free variables.
As a result, explicit variable substitution (common in de Bruijn serial & named variable stynax) and fuel tower (common in PHOAS) can both be avoided

[UIDEquiv.getUID] and [UIDEquiv.inv] are inverse: [UIDEquiv.leftInv] starts
from a value, while [UIDEquiv.rightInv] starts from a UID.
-/
structure UIDEquiv (UID : TIndex) (V : Type) : Type where
  getUID : (value : V) → UID
  inv : (id : UID) → V
  leftInv : ∀ (value : V), inv (getUID value) = value
  rightInv : ∀ (id : UID), getUID (inv id) = id

namespace Free

abbrev Fixpoint (self : Free) (V : Type) :=
  UIDEquiv self.Index V

end Free

namespace UIDEquiv

/--
extension of [UIDEquiv] that can attach metadata `M : Type/Prop` to existing UID-value pairs:

- [UIDEquiv.Aux.saveMeta] requires both value and its metadata, but UID is only computed from value
- [UIDEquiv.Aux.loadMeta] requires both UID and the evidence that its metadata has been saved before
- all [UIDEquiv.Aux] instances derived from the same [UIDEquiv] share its [UIDEquiv.getUID] and [UIDEquiv.inv]

`M` is a dependent family over `V` and is reconstructed by each [UIDEquiv.Aux]
instance through [UIDEquiv.Aux.loadMeta]. [UIDEquiv.Aux.Evidence] restricts that
reconstruction to identifiers carrying evidence for the auxiliary instance.

[UIDEquiv.Aux.saveMeta] saves a bundle using only its value through the shared group bridge.
[UIDEquiv.Aux.loadMeta] reconstructs a value through the group and then this instance's metadata.
-/
class Aux {UID : TIndex} {V : Type}
    (outer : UIDEquiv UID V) (M : V → Sort u) where
  Evidence : UID → Type
  lookup : (id : UID) → Option (Evidence id) -- TODO: this shouldn't be useful
  saveMeta : (bundle : PSigma M) → Evidence (outer.getUID bundle.fst)
  loadMeta : (ev: PSigma Evidence) → M (outer.inv ev.fst)

namespace Aux
section variable {UID : TIndex} {V : Type} {group : UIDEquiv UID V} {D : V → Sort u}

/-- Saving membership and reconstructing metadata preserves the original value. -/
@[simp]
theorem leftInvValue (self : Aux group D) (bundle : PSigma D) :
    (⟨group.inv (group.getUID bundle.fst),
      self.loadMeta
        ⟨group.getUID bundle.fst, self.saveMeta bundle⟩⟩ : PSigma D).fst = bundle.fst :=
  group.leftInv bundle.fst

end
end Aux
end UIDEquiv

attribute [simp] UIDEquiv.leftInv UIDEquiv.rightInv

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
