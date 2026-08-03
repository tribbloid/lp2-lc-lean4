
import «Lp2lc».Active.Shared

namespace Lp2lc.Active.Util

abbrev TIndex := Type
abbrev TData := Type

/--
collection of free type variables used in HOAS bindings

They are deliberately left free to ward off unlawful construction:

- the only way to construct an `Index` is to get the UID of a `Value` through the fixpoint bridge
- the only way to construct a `Data` is to parse a primitive literal in AST
-/
class Free : Type 1 where
  Index : TIndex
  -- Ev : Index -> Prop := λ _ => True -- TODO: this should be moved out from Free
  Data : TData

namespace Free

@[reducible] def mkWeakest (Index : TIndex) (Data : TData) : Free :=
  { Index := Index, Data := Data }

/-- Replaces a free family with its peer whose evidence predicate is `True`. -/
@[reducible] def weaken (self : Free) : Free :=
  mkWeakest self.Index self.Data

instance weakenCoe (Index : TIndex) (Data : TData) :
    Coe Index {index : Index // (mkWeakest Index Data).Ev index} :=
  ⟨λ index => ⟨index, True.intro⟩⟩

end Free

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

namespace UIDEquiv

class Aux0 {UID : TIndex} {V : Type}
    (outer : UIDEquiv UID V) (M : V → Sort u) where
  getEv : (bundle : PSigma M) → outer.getUID bundle.fst
  invEv : (uid: UID) → M (outer.inv ev)

/--
extension of [UIDEquiv] that can attach metadata `M : Type/Prop` to existing UID-value pairs:

- [UIDEquiv.Aux.getEv] requires both value and its metadata, but UID is only computed from value
- [UIDEquiv.Aux.invEv] requires both UID and the evidence that its metadata has been saved before
- all [UIDEquiv.Aux] instances derived from the same [UIDEquiv] share its [UIDEquiv.getUID] and [UIDEquiv.inv]

`M` is a dependent family over `V` and is reconstructed by each [UIDEquiv.Aux]
instance through [UIDEquiv.Aux.invEv]. [UIDEquiv.Aux.Ev] restricts that
reconstruction to identifiers carrying evidence for the auxiliary instance.

[UIDEquiv.Aux.getEv] saves a bundle using only its value through the shared group bridge.
[UIDEquiv.Aux.invEv] reconstructs a value through the group and then this instance's metadata.
-/
class Aux {UID : TIndex} {V : Type}
    (outer : UIDEquiv UID V) (M : V → Sort u) where
  Ev : UID → Prop
  getEv : (bundle : PSigma M) → Ev (outer.getUID bundle.fst)
  invEv : (ev: PSigma Ev) → M (outer.inv ev.fst)

namespace Aux

section variable {UID : TIndex} {V : Type} {outer : UIDEquiv UID V} {M : V → Sort u} (self : Aux outer M)

abbrev AuxUID := PSigma self.Ev

/-- Saving membership and reconstructing metadata preserves the original value. -/
@[simp]
theorem leftInvValue (bundle : PSigma M) :
    (⟨outer.inv (outer.getUID bundle.fst),
      self.invEv
        ⟨outer.getUID bundle.fst, self.getEv bundle⟩⟩ : PSigma M).fst = bundle.fst :=
  outer.leftInv bundle.fst

end
end Aux

end UIDEquiv

namespace Free

abbrev Fixpoint (F : Free) (V : Type) :=
  UIDEquiv F.Index V

class HasFixpoint (F: Free) : Type 1 where
  mkFixpoint (V: Type) : Free.Fixpoint F V
  mkAux {UID : TIndex} {V : Type} (outer : UIDEquiv UID V) (M : V -> Type) : UIDEquiv.Aux outer M

end Free

attribute [simp] UIDEquiv.leftInv UIDEquiv.rightInv

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
