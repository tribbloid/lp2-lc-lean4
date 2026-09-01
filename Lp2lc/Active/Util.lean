
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
Receipt-indexed bridge between values and identifiers. Read-only.

The value family is indexed by this bridge's evidence so recursive PHOAS
carriers can retain the receipt required by `get`.

type VK is deliberately a type constructor of V, without it V may be impossible to define due to cyclic references
-/
class UIdView (VK : UIdU → Sort u) where
  UId : UIdU
  get : (uid : UId) → VK UId

/--
Full receipt-indexed bridge, extending [UIdView] with the reverse direction.

`inv` is the only way to obtain a UId: it requires a value, so a view alone
cannot mint receipts from new values.

By default it is not extendable, if you need to use the hypothetical `mkLesser`, use [UIdEquiv.Extendable]
-/
class UIdEquiv {VK} (base: UIdView VK) where
  inv (value : VK base.UId) : base.UId
  rightInv : ∀ (value : VK base.UId), base.get (inv value) = value
  leftInv : ∀ (receipt : base.UId), inv (base.get receipt) = receipt

namespace UIdView

class HasEv (UId : UIdU) where
  Ev : UId → Prop -- a subtype of UId with extra contract

/-
FIXME: this section should be moved into proper doc string
`Lesser` maps both the UId and value of a `UIdView` to their respective subtypes,
while `Greater` maps both to explicitly supplied supertypes.

The supertypes are represented by new type arguments for both `UId` and `VK`,
each accompanied by its upcast function. `Extendable` supports both directions.

Math discovery relies on continuous supertyping (e.g. N -> Q), not only
subtyping, so `UIdEquiv` supports both directions.
-/

/-- Read-only metadata view over a subtype of receipts from `base`. -/
class Lesser {VK} (base : UIdView VK)
  (annotateV : (v : VK base.UId) → Sort v) -- FIXME: should be a class member
    extends HasEv base.UId where
  get {uid} (receipt : Ev uid) : annotateV (base.get uid)

/-- Extends a read-only view with symmetric `get` access over wider carriers. -/
class Greater {VK VK2} (base : UIdView VK)
   extends UIdView VK2 where
  upcastUId : base.UId -> UId
  upcastV : VK base.UId -> VK2 UId
  getUpcast : ∀ (receipt : base.UId), -- FIXME: bad name, predicates/axioms should
    get (upcastUId receipt) = upcastV (base.get receipt)

-- FIXME: we don't need Coe here
-- /-- Coerces a greater view to the widened read-only view that it contains. -/
-- instance {VK VK2} {base : UIdView VK} :
--     CoeOut (Greater base VK2) (UIdView VK2) where
--   coe self := self.toUIdView

end UIdView

namespace UIdEquiv

/-- Coerces a full bridge to the read-only view that it completes. -/
instance {VK} {base : UIdView VK} : CoeOut (UIdEquiv base) (UIdView VK) where
  coe _self := base

/-- Adds a reverse metadata bridge that is lawful for every equivalence over `base`. -/
class Lesser {VK} {base : UIdView VK} (VK2 : (v : VK base.UId) → Sort v)
    extends UIdView.Lesser base VK2 where
  inv (outer : UIdEquiv base) {v} (tagged : VK2 v) : Ev (outer.inv v)
  rightInv : ∀ (outer : UIdEquiv base) {v} (tagged : VK2 v),
    HEq (get (inv outer tagged)) tagged
  leftInv : ∀ (outer : UIdEquiv base) {uid} (receipt : Ev uid),
    HEq (inv outer (get receipt)) receipt := by
      intro _outer _uid receipt
      exact proof_irrel_heq _ receipt

/-- Adds a lawful inverse to a widened read-only view. -/
class Greater {VK} {base : UIdView VK} (VK2 : UIdU → Sort v)
    extends UIdView.Greater (VK2 := VK2) base where
  inv (outer : UIdEquiv base) (value : VK2 UId) : UId
  -- FIXME: prove the following if possible
  rightInv : ∀ (outer : UIdEquiv base) (value : VK2 UId),
    get (inv outer value) = value
  leftInv : ∀ (outer : UIdEquiv base) (receipt : UId),
    inv outer (get receipt) = receipt

/-- Extends a base equivalence with lawful subtype metadata and supertype bridges. -/
class Extendable {VK} (base : UIdView VK) extends UIdEquiv base where
  mkLesser (Tagging : VK base.UId → Sort u) : Lesser Tagging
  mkGreater (VK2 : UIdU → Sort u) : Greater (base := base) VK2

end UIdEquiv

attribute [simp] UIdEquiv.rightInv UIdEquiv.leftInv
  UIdEquiv.Lesser.rightInv UIdEquiv.Lesser.leftInv
  UIdEquiv.Greater.rightInv UIdEquiv.Greater.leftInv

/--
Owns the data representation `D`, the binary data type of primitive literals.

The only way to construct `D` is to parse a primitive literal in AST.
-/
class HasData where
  D : DataU -- Binary Data type

/--
the meaning of P in PHOAS, the collection of free type variables used in PHOAS bindings

They are deliberately left free to ward off unlawful construction:

- the only way to construct `F` and `B` is to get the UId of something already existing through [UIdEquiv]
- the only way to construct `D` is to parse a primitive literal in AST
-/
class Parameters extends HasData where
  F : UIdU -- free receipt carrier, AKA captured variable binding
  B : UIdU -- bound receipt carrier, introduced per binder by [AST.lam]

namespace Parameters

/-- Maps the free, bound, and data carriers of one syntax parameter set into another. -/
@[ext]
structure CarrierMap (P Q : Parameters) where
  mapF : P.F → Q.F
  mapB : P.B → Q.F ⊕ Q.B
  mapD : P.D → Q.D

namespace CarrierMap

/-- Leaves free and data carriers unchanged and keeps bound references bound. -/
def identity (P : Parameters) : CarrierMap P P where
  mapF := id
  mapB := Sum.inr
  mapD := id

/-- Applies a carrier map to a free-or-bound reference. -/
def mapRef {P Q : Parameters} (self : CarrierMap P Q) : P.F ⊕ P.B → Q.F ⊕ Q.B
  | .inl free => .inl (self.mapF free)
  | .inr bound => self.mapB bound

/-- Composes two carrier maps in source-to-target order. -/
def «then» {P Q R : Parameters} (self : CarrierMap P Q)
    (next : CarrierMap Q R) : CarrierMap P R where
  mapF := λ free => next.mapF (self.mapF free)
  mapB := λ bound => next.mapRef (self.mapB bound)
  mapD := λ repr => next.mapD (self.mapD repr)

/-- Extends a carrier map beneath one structural lambda binder. -/
def underBinder {P Q : Parameters} (self : CarrierMap P Q) :
    CarrierMap { P with B := P.B ⊕ Unit } { Q with B := Q.B ⊕ Unit } where
  mapF := self.mapF
  mapB
    | .inl outer =>
      match self.mapB outer with
      | .inl free => .inl free
      | .inr target => .inr (.inl target)
    | .inr () => .inr (.inr ())
  mapD := self.mapD

/-- Replaces the newest structural slot while mapping all outer carriers. -/
def bind {P Q : Parameters} (self : CarrierMap P Q) (arg : Q.F ⊕ Q.B) :
    CarrierMap { P with B := P.B ⊕ Unit } Q where
  mapF := self.mapF
  mapB
    | .inl outer => self.mapB outer
    | .inr () => arg
  mapD := self.mapD

@[simp]
theorem underBinderThen {P Q R : Parameters} (first : CarrierMap P Q)
    (second : CarrierMap Q R) :
    first.underBinder.«then» second.underBinder = (first.«then» second).underBinder := by
  ext value
  · rfl
  · cases value with
    | inl outer =>
      cases hFirst : first.mapB outer with
      | inl free => simp [«then», mapRef, underBinder, hFirst]
      | inr target =>
        cases hSecond : second.mapB target <;>
          simp [«then», mapRef, underBinder, hFirst, hSecond]
    | inr newest => cases newest; simp [«then», mapRef, underBinder]
  · rfl

@[simp]
theorem bindThen {P Q R : Parameters} (first : CarrierMap P Q)
    (second : CarrierMap Q R) (arg : Q.F ⊕ Q.B) :
    (first.bind arg).«then» second =
      (first.«then» second).bind (second.mapRef arg) := by
  ext value
  · rfl
  · cases value with
    | inl outer => rfl
    | inr newest => cases newest; rfl
  · rfl

@[simp]
theorem identityThen {P Q : Parameters} (self : CarrierMap P Q) :
    (identity P).«then» self = self := by
  ext value <;> rfl

end CarrierMap

end Parameters

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

def ifSucceedMustSatisfy (condition: T -> Prop := λ _ => True) : Prop :=
  ∀ (fuel : Nat), match (self fuel) with
  | .yield (some v) => condition v
  | _ => true

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
