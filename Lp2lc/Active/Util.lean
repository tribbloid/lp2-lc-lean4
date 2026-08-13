
import «Lp2lc».Active.Shared

namespace Lp2lc.Active.Util

abbrev TIndex := Type
abbrev TData := Type

/--
collection of free type variables used in HOAS bindings

They are deliberately left free to ward off unlawful construction:

- the only way to construct an `Index` is to get the UId of a `Value` through the fixpoint bridge
- the only way to construct a `Data` is to parse a primitive literal in AST
-/
class Free : Type 1 where
  Carrier : TIndex -- AKA variable binding
  Data : TData

namespace Free

@[reducible] def mkWeakest (Index : TIndex) (Data : TData) : Free :=
  { Carrier := Index, Data := Data }

/-- Replaces a free family with its peer whose evidence predicate is `True`. -/
@[reducible] def weaken (self : Free) : Free :=
  mkWeakest self.Carrier self.Data

end Free

/--
thin wrapper of `T` representing outcome of a valid compilation, implying safety of associated code snippet.

all compilation API should ideally return this.

if registered in a [UIdEquiv], the result UId should work in any `Env` to get a compatible term or value.
-/
structure Valid T : Type where
  self: T

class HasEv (UId : TIndex) where
  Ev : UId → Prop

abbrev HasEv.Receipt (self : HasEv UId) := PSigma self.Ev

/--
Hypothetical bridge between values & UIds as HOAS carrier

[UIdEquiv.getUId] is the only way to obtain a UId: it requires a `V`.
Consequently, [UIdEquiv.inv] is total without introducing free variables.
As a result, explicit variable substitution (common in de Bruijn serial & named variable stynax) and fuel tower (common in PHOAS) can both be avoided

[UIdEquiv.getUId] and [UIdEquiv.inv] are inverse: [UIdEquiv.leftInv] starts
from a value, while [UIdEquiv.rightInv] starts from a UId.
-/
structure UIdEquiv (UId : TIndex) (V : Type) : Type where
  getUId : (value : V) → UId
  inv : (id : UId) → V
  leftInv : ∀ (value : V), inv (getUId value) = value
  rightInv : ∀ (id : UId), getUId (inv id) = id

namespace UIdEquiv

/--
extension of [UIdEquiv] that can attach metadata `M : Type/Prop` to existing UId-value pairs:

- [UIdEquiv.Aux.getEv] requires both value and its metadata, but UId is only computed from value
- [UIdEquiv.Aux.invEv] requires both UId and the evidence that its metadata has been saved before
- all [UIdEquiv.Aux] instances derived from the same [UIdEquiv] share its [UIdEquiv.getUId] and [UIdEquiv.inv]

`M` is a dependent family over `V` and is reconstructed by each [UIdEquiv.Aux]
instance through [UIdEquiv.Aux.invEv]. [UIdEquiv.Aux.Receipt] restricts that
reconstruction to identifiers carrying evidence for the auxiliary instance.

[UIdEquiv.Aux.getEv] saves a bundle using only its value through the shared group bridge.
[UIdEquiv.Aux.invEv] reconstructs a value through the group and then this instance's metadata.
-/
class Aux {UId : TIndex} {V : Type}
    (outer : UIdEquiv UId V) (M : V → Sort u) extends HasEv UId where
  getEv : (bundle : PSigma M) → Ev (outer.getUId bundle.fst)
  invEv : (rc : PSigma Ev) → M (outer.inv rc.fst)

namespace Aux

section variable {UId : TIndex} {V : Type} {outer : UIdEquiv UId V} {M : V → Sort u} (self : Aux outer M)

/-- Saving membership and reconstructing metadata preserves the original value. -/
@[simp]
theorem leftInvValue (bundle : PSigma M) :
    (⟨outer.inv (outer.getUId bundle.fst),
      self.invEv
        ⟨outer.getUId bundle.fst, self.getEv bundle⟩⟩ : PSigma M).fst = bundle.fst :=
  outer.leftInv bundle.fst

end
end Aux

end UIdEquiv

namespace Free

/-
TODO: Specification of improved UIdEquiv:

- UId type must be associated with values
- it should be impossible to mix UId for different values or Equiv
-/

abbrev Fixpoint (F : Free) (V : Type) :=
  UIdEquiv F.Carrier V

universe u

/-- Constructs fixpoint bridges and universe-polymorphic metadata bridges for a free family. -/
class HasFixpoint (F : Free) : Type (max 1 u) where
  mkFixpoint (V : Type) : Free.Fixpoint F V
  mkAux {UId : TIndex} {V : Type} (outer : UIdEquiv UId V) (M : V → Sort u) : UIdEquiv.Aux outer M

abbrev HF2.Fixpoint (UId V : Type) :=
  UIdEquiv UId V

class HF2 (VV : Type) : Type (max 1 u) extends Free where
  UId : Type
  Carrier := UId × HF2.Fixpoint UId VV
  mkFixpoint (V : Type) : HF2.Fixpoint UId V
  mkAux {UId : TIndex} {V : Type} (outer : UIdEquiv UId V) (M : V → Sort u) : UIdEquiv.Aux outer M


end Free

attribute [simp] UIdEquiv.leftInv UIdEquiv.rightInv

section variable {T : Sort u}

namespace Rec

/-- Fuel-guarded semantic result used by executable interpreters and compilers. -/
inductive Outcome (T : Sort u)
  | yield (v : T)
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

end Rec

-- universe u v
def Rec (T : Sort u) := (fuel : Nat) -> @Rec.Outcome T

-- LATER: all algorithm with this signature should have a proof of monotonicity

namespace Rec
section variable (self : Lp2lc.Active.Util.Rec T)

/-- Recursive computations stay successful with more fuel for the same result. -/
def Monotone : Prop :=
  ∀ (less more : Nat) (value : T),
  (less <= more) ->
  self less = .yield value ->
  self more = .yield value


end

abbrev OutcomeOpt (T : Type u) := Rec.Outcome (Option T)
end Rec

abbrev RecOpt (T : Type u) := Rec (Option T)

namespace RecOpt
section variable {T : Type u} (self : RecOpt T)

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
  let hasFuel := RecOpt.isDecidable self (λ v => v = expectedV)
  let noFuel := self 0 = .outOfFuel
  hasFuel /\ noFuel

def shouldFail : Prop :=
  let hasFuel := ∃ (fuel : Nat), match (self fuel) with
  | .yield none => true
  | _ => false
  let noFuel := self 0 = .outOfFuel
  hasFuel /\ noFuel

end
end RecOpt

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
