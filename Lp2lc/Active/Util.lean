
import «Lp2lc».Active.Shared

namespace Lp2lc.Active.Util

/-- Bundles an upcast with injectivity so refined values cannot collapse. -/
structure Embedding (α : Sort u) (β : Sort v) where
  toFun (value : α) : β
  inj' : Function.Injective toFun

infixr:25 " ↪ " => Embedding -- stolen from Mathlib

instance {α : Sort u} {β : Sort v} : CoeFun (α ↪ β) (λ _ => α → β) where
  coe self := self.toFun

abbrev UCarrier := Type -- the `U` prefix signifies this symbol as denoting a universe level
abbrev UByteCode := Type


-- /--
-- contract that relates `KVRefs` to its Lesser/Greater versions

-- they must all use the same Key type, and given any 2 value types, the upcast function must be globally unique
-- -/
-- structure Schema where
--   K : UCarrier
--   upcastV (V1 : Sort u) (V2 : Sort v) : Embedding V1 V2

/-- Read-only lookup from receipt keys to values. -/
structure KVRefs (K : UCarrier) (V : Sort u) where
  get : K → V


namespace KVRefs
section variable {K V} (this : KVRefs K V)


def Unit (K) := KVRefs K PUnit

/-- Read-only access to a larger carrier, preserving the base receipt mapping. -/
structure Greater (K2 V2) extends KVRefs K V2 where
  upcastK : Embedding K2 K
  upcastV : Embedding V V2 -- distinguishes views made with different value embeddings
  equivariance : ∀ (receipt : K), get receipt = upcastV (this.get receipt)

structure HasEv (K : UCarrier) where
  ev : K → Prop -- a subtype of UId with extra contract

namespace HasEv
section variable (this: HasEv K)

def UId := {x : K // this.ev x}

end
end HasEv

structure Lesser (K2 V2) extends KVRefs K2 V2 where
  upcastK : Embedding K2 K
  upcastV : Embedding V2 V
  equivariance : ∀ (receipt : K2), upcastV (get receipt) = this.get (upcastK receipt)

-- /-- Read-only access to refined receipts compatible with a base view. -/
-- structure Lesser (V2)
--     extends HasEv K, KVRefs {uid // ev uid} V2 where
--   upcastV : Embedding V2 V
--   equivariance : ∀ (receipt : {uid // ev uid}), upcastV (get receipt) = this.get receipt.val

structure Adapter (K2 V2) where
  specify : this.Lesser K2 V2 -- converts a KVRefs to its Lesser view
  widen : this.Greater K2 V2 -- converts a KVRefs to its Greater view

end
end KVRefs

-- /--
-- Unlike [KVRefs], the key type `UId` is not shared with other value types, so `get` cannot produce nonexistent values.

-- The type `V_` is deliberately a type constructor of `V`; otherwise cyclic references may prevent defining `V`.
-- -/
-- structure UIdRefs (V_ : UCarrier → Sort u) extends HasUId, KVRefs UId (V_ UId)

/-- A bijective lookup: `inv` returns the canonical receipt for a value, with both inverse laws. -/
structure KVEquiv {K V} (base : KVRefs K V) where
  inv (value : V) : K
  rightInv : ∀ (value : V), base.get (inv value) = value
  leftInv : ∀ (k : K), inv (base.get k) = k

namespace KVEquiv
section variable {K V} {refs : KVRefs K V}

structure Adapter (this : KVEquiv refs) {K2 V2} (forRefs: refs.Adapter K2 V2) where
  specify :
    let refs2 := forRefs.specify
    KVEquiv refs2.toKVRefs
  widen :
    let refs2 := forRefs.widen
    KVEquiv refs2.toKVRefs

end
end KVEquiv

-- /--
-- Has a dependent unique ID.
-- -/
-- structure HasDepUId (T: Type) where
--   DepUId : T -> UCarrier

-- structure KKVEquiv {K1 K2 V} (base : KVRefs (K1 × K2) V) where
--   inv (k1 : K1) (value : V) : K2
--   rightInv : ∀ (k1 value), base.get (k1, inv k1 value) = value
--   leftInv : ∀ (k1 k2), inv k1 (base.get (k1, k2)) = k2

attribute [simp] KVEquiv.rightInv KVEquiv.leftInv

/-- Supplies the bytecode representation of primitive literals. -/
structure HasByteCode where
  B : UByteCode -- Binary Data type

/-- Syntax contexts and their increment operation; lexical indices are distinct from runtime value receipts. -/
structure Parameters extends HasByteCode where
  TIndex : UCarrier -- lexical context/index
  index : TIndex
  inc : TIndex → TIndex

/-- A proxy tied to an index type, so it survives updates to a Parameters context. -/
inductive IndexProxy (Index : UCarrier) : Index → Type where
| only {C : Index} : IndexProxy Index C

namespace Parameters
section variable (this : Parameters)

abbrev nextIndex: this.TIndex := this.inc this.index

abbrev Proxy := IndexProxy this.TIndex

def TRef : Type := this.Proxy this.index

abbrev Next : Parameters :=
  {B := this.B, TIndex := this.TIndex, index := this.nextIndex, inc := this.inc}

def NextTRef : Type := this.Next.TRef

/-- An erased witness that a context is reachable by extending an earlier context. -/
inductive Lesser (i1 : this.TIndex) : this.TIndex → Prop where
| refl : Lesser i1 i1
| step {i2} (prior : Lesser i1 i2) : Lesser i1 ({this with index := i2}).Next.index


end
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

-- LATER: All algorithms with this signature should have a proof of monotonicity.

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

/--
Whether `self` needs exactly `fuelBudget` fuel to evaluate to `expectedV`.

It requires both that `fuelBudget` fuel yields `expectedV`, and that one less
fuel runs out, pinning the exact fuel cost of the evaluation.
-/
def shouldYieldsBool (fuelBudget : Nat) (expectedV : T) [BEq T] : Bool :=
  (match self fuelBudget with
    | .yield (some value) => value == expectedV
    | _ => false) &&
  (match self (fuelBudget - 1) with
    | .outOfFuel => true
    | _ => false)

/--
Whether `self` needs exactly `fuelBudget` fuel to deterministically fail.

It requires both that `fuelBudget` fuel reaches `.yield none`, and that one less
fuel runs out, pinning the exact fuel cost of the failure.
-/
def shouldFailBool (fuelBudget : Nat) : Bool :=
  (match self fuelBudget with
    | .yield none => true
    | _ => false) &&
  (match self (fuelBudget - 1) with
    | .outOfFuel => true
    | _ => false)

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
