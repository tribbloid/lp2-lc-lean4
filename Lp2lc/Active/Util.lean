
import «Lp2lc».Active.Shared

namespace Lp2lc.Active.Util

abbrev UIdU := Type -- the `U` suffix signifies this symbol as denoting a universe level
abbrev DataU := Type

class HasEv (UId : UIdU) where
  Ev : UId → Prop

abbrev HasEv.Receipt (self : HasEv UId) := PSigma self.Ev

/--
Hypothetical bridge between values & UIds as HOAS carrier

[UIdEquiv.inv] is the only way to obtain a UId: it requires a `V`.
Consequently, [UIdEquiv.get] is total without introducing free variables.
As a result, explicit variable substitution (common in de Bruijn serial & named variable stynax) and fuel tower (common in PHOAS) can both be avoided

[UIdEquiv.inv] and [UIdEquiv.get] are inverse: [UIdEquiv.rightInv] starts
from a value, while [UIdEquiv.leftInv] starts from a UId.
-/
class UIdEquiv (UId : UIdU) (V : Type) : Type where
  inv : (value : V) → UId
  get : (id : UId) → V
  rightInv : ∀ (value : V), get (inv value) = value
  leftInv : ∀ (id : UId), inv (get id) = id


/-
TODO: Avoid fake construction through UIdEquiv

the above code allow the same type of UId to be generated from different instances, this has caused serious problem in the constructive proof as it allow fake V to be created.

I'd like to plug this loophole:

- UIdEquiv should be a subclass of `HasEv` (similar to Aux)
- `inv` should return `Ev UId`, get should consume it
- other functions should adapt
- AST in type system definitions are mostly intact
  - but when being used in BuildEnv and ExeEnv, their original Carrier will no longer be able to carry the receipts of `trm2valCtx`/`trm2TypCtx`
  - therefore, new carriers defined by `F.WithEv` have to be used instead:
    - `CVar` := Carrier for trm2valCtx
    - `CTyp` := Carrier for trm2typCtx
    - `Trm.eval` accepts `Trm CVar` and produce `Trm CVar`
    - `Trm.infer` accepts `Trm CVar` and produce `Typ CTyp`, since some `Trm CVar` may contain `.ref` to free variables assigned `trm2valCtx`, the new `BuildEnv` will need access to both `trm2valCtx` and `trm2TypCtx` to work properly

This is a large-scale migration, you should gradually migrate existing code to a new directory/package `Lp2lc/Next`, in multiple steps & git commits.

- For a component, definition and implementation/discharge should be migrated in 2 different commits
- After each commit, you must ask for permission before proceeding to the next step

The following code are strictly prohibited, every commit should be followed by a subagent that warn against such violations:

- duplicated definition (e.g. duplicated inductive cases in multiple definitions)
- leaky abstraction & unnecessary copy & paste
- moving/weakening goalpost (e.g. adding axiom, modifying theorem signature)
- bloated code after migration
- introducing new/exotic concept that doesn't exist in original code

-/

namespace UIdEquiv

/-- Value bundled with its metadata over `M`. -/
abbrev Bundle {V : Type} (M : V → Sort u) := PSigma M

/-- UId bundled with its evidence from `Ev`. -/
abbrev Receipt {UId : UIdU} (Ev : UId → Prop) := PSigma Ev

/--
extension of [UIdEquiv] that can attach metadata `M : Type/Prop` to existing UId-value pairs:

- [UIdEquiv.Aux.inv] requires both value and its metadata, but UId is only computed from value
- [UIdEquiv.Aux.get] requires both UId and the evidence that its metadata has been saved before
- all [UIdEquiv.Aux] instances derived from the same [UIdEquiv] share its [UIdEquiv.inv] and [UIdEquiv.get]

`M` is a dependent family over `V` and is reconstructed by each [UIdEquiv.Aux]
instance through [UIdEquiv.Aux.get]. [UIdEquiv.Receipt] restricts that
reconstruction to identifiers carrying evidence for the auxiliary instance.

[UIdEquiv.Aux.inv] saves a bundle using only its value through the shared group bridge.
[UIdEquiv.Aux.get] reconstructs a value through the group and then this instance's metadata.
-/
class Aux {UId : UIdU} {V : Type}
    (outer : UIdEquiv UId V) (M : V → Sort u) extends HasEv UId where
  inv : (bundle : Bundle M) → Ev (outer.inv bundle.fst)
  get : (rc : Receipt Ev) → M (outer.get rc.fst)

namespace Aux

section variable {UId : UIdU} {V : Type} {outer : UIdEquiv UId V} {M : V → Sort u} (self : Aux outer M)

/-- Saving membership and reconstructing metadata preserves the original value. -/
@[simp]
theorem rightInvValue (bundle : Bundle M) :
    (⟨outer.get (outer.inv bundle.fst),
      self.get
        ⟨outer.inv bundle.fst, self.inv bundle⟩⟩ : Bundle M).fst = bundle.fst :=
  outer.rightInv bundle.fst

end
end Aux

end UIdEquiv

/--
collection of free type variables used in HOAS bindings

They are deliberately left free to ward off unlawful construction:

- the only way to construct an `Index` is to get the UId of a `Value` through the fixpoint bridge
- the only way to construct a `Data` is to parse a primitive literal in AST
-/
class Free : Type 1 where
  Carrier : UIdU -- AKA variable binding
  Data : DataU

namespace Free
section variable (this : Free)

abbrev Fixpoint (V : Type) :=
  UIdEquiv this.Carrier V

universe u

/-- Constructs fixpoint bridges and universe-polymorphic metadata bridges for a free family. -/
class FixpointCtor : Type (max 1 u) where
  mkFixpoint (V : Type) : this.Fixpoint V
  attachAux {UId : UIdU} {V : Type} (outer : this.Fixpoint V) (M : V → Sort u) : UIdEquiv.Aux outer M

/--
Extending the Carrier of a Free instance by [HasEv.Ev]

This class is frequently used to define PHOAS AST with new, conpartmentalised carrier type
-/
class WithEv (augmentation: HasEv this.Carrier) extends Free where
  Carrier := augmentation.Receipt
  Data := this.Data

end
end Free

attribute [simp] UIdEquiv.rightInv UIdEquiv.leftInv

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
