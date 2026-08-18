
import «Lp2lc».Active.Shared

namespace Lp2lc.Active.Util

abbrev UIdU := Type -- the `U` suffix signifies this symbol as denoting a universe level
abbrev DataU := Type

universe u v

inductive Label
| typ
| trm
| val

/--
Receipt-indexed bridge between values and identifiers.

The value family is indexed by this bridge's evidence so recursive PHOAS
carriers can retain the receipt required by `get`.

type V is deliberately a type constructor of V, without it V may be impossible to define due to cyclic references
-/
class UIdEquiv (VK : UIdU → Type u) where
  UId : UIdU
  get : (uid : UId) → VK UId
  inv : (value : VK UId) → UId
  rightInv : ∀ (value : VK UId), get (inv value) = value
  leftInv : ∀ (receipt : UId), inv (get receipt) = receipt

namespace UIdEquiv

class HasEv (UId : UIdU) where
  Ev : UId → Prop -- used to represent subtype of UId, implying extra condition

/-
TODO: I don't think subtyping/`Lesser` is general enough, we need supertyping/`Greater`

Math discovery relies on continuous supertyping (e.g. N -> Q), not subtyping. The design of UIdEquiv should be compatible to both directions
-/

/-- an auxiliary equivalence for a subtype of [outer.VK T], Can attach independently witnessed metadata `M` to receipts from outer bridge. -/
class Lesser {VK : UIdU → Type u}
    (outer : UIdEquiv VK) (M : VK outer.UId → Sort v)
    extends HasEv outer.UId where
  get : (receipt : PSigma toHasEv.Ev) → M (outer.get receipt.fst)
  inv : (bundle : PSigma M) → Ev (outer.inv bundle.fst)

end UIdEquiv

attribute [simp] UIdEquiv.rightInv UIdEquiv.leftInv

/--
the meaning of P in PHOAS, the collection of free type variables used in PHOAS bindings

They are deliberately left free to ward off unlawful construction:

- the only way to construct `C` is to get the UId of something already existing through [UIdEquiv]
- the only way to construct `D` is to parse a primitive literal in AST
-/
class Parameters where
  C : UIdU -- Carrier type, AKA variable binding
  D : DataU -- Binary Data type

namespace Free

/-- Receipt-indexed fixpoint bridge: its `UId` type is the receipt carrier, values are indexed by it. -/
abbrev Fixpoint (VK : UIdU → Type u) :=
  UIdEquiv VK

/-- Constructs receipt-indexed fixpoint bridges. -/
class FixpointCtor where
  mkFixpoint (VK : UIdU → Type u) : Fixpoint VK

end Free

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
