
import «Lp2lc».Active.Shared

namespace Lp2lc.Active.Util

/-- Bundles an upcast with injectivity so refined values cannot collapse. -/
structure Embedding (α : Sort u) (β : Sort v) where
  toFun (value : α) : β
  inj' : Function.Injective toFun

infixr:25 " ↪ " => Embedding -- stolen from Mathlib

instance {α : Sort u} {β : Sort v} : CoeFun (α ↪ β) (λ _ => α → β) where
  coe self := self.toFun

abbrev KU := Type -- the `U` suffix signifies this symbol as denoting a universe level
abbrev DataU := Type

-- universe u v TODO: can remove

inductive Label
| typ
| trm
| val


-- /--
-- contract that relates `KVRefs` to its Lesser/Greater versions

-- they must all use the same Key type, and given any 2 value types, the upcast function must be globally unique
-- -/
-- structure Schema where
--   K : KU
--   upcastV (V1 : Sort u) (V2 : Sort v) : Embedding V1 V2

/--
Receipt-indexed bridge between values and PHOAS carriers. Read-only.

The value family is indexed by this bridge's evidence so recursive PHOAS
carriers can retain the receipt required by `get`.
-/
structure KVRefs (K : KU) (V : Sort u) where
  get : K → V


namespace KVRefs
section variable {K V} (this : KVRefs K V)


def Unit (K) := KVRefs K PUnit

--FIXME: rewrite the following definition using the new "Schema" contract: due to the uniqueness of upcastV, all the following types only need to depend on V2, not V ↪ V2

/-- Read-only access to a larger carrier, preserving the base receipt mapping. -/
structure Greater (K2 V2) extends KVRefs K V2 where
  upcastK : Embedding K2 K
  upcastV : Embedding V V2 -- this is not important, but it also means (g1 : base.Greater X) != (g2 : base.Greater X) unless the same expression is used to generate them
  equivariance : ∀ (receipt : K), get receipt = upcastV (this.get receipt)

structure HasEv (K : KU) where
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

-- FIXME: In KVRefs.Adapter & KVEquiv.Adapter, the following functions should be renamed to "Widen" and "Specify"
structure Adapter (K2 V2) where
  shrink : this.Lesser K2 V2 -- converting a KVRefs to it's Lesser
  expand : this.Greater K2 V2 -- converting a KVRefs to it's Greater

end
end KVRefs

structure HasUId where --> SharedUID
  UId : KU

-- /--
-- Unlike [KVRefs], the key type `UId` is not shared with any other value type, so `get` cannot be abused to non-existing value.

-- type `V_` is deliberately a type constructor of `V`, without it V may be impossible to define due to cyclic references
-- -/
-- structure UIdRefs (V_ : KU → Sort u) extends HasUId, KVRefs UId (V_ UId)

/--
Full receipt-indexed bridge, extending [KVRefs] with the reverse direction.

`inv` is the only way to obtain a `K`: it requires a value, a view alone cannot mint receipts from new values.
-/
structure KVEquiv {K V} (base : KVRefs K V) where
  inv (value : V) : K
  rightInv : ∀ (value : V), base.get (inv value) = value
  leftInv : ∀ (receipt : K), inv (base.get receipt) = receipt

namespace KVEquiv
section variable {K V} {refs : KVRefs K V}

-- FIXME: shorten using section variable, no need to be CoeOut
/-- Coerces a full bridge to the read-only view that it completes. -/
instance {K V} (base : KVRefs K V) : CoeOut (KVEquiv base) (KVRefs K V) where -- TODO: why do I need this?
  coe _self := base

structure Adapter (this : KVEquiv refs) {K2 V2} (forRefs: refs.Adapter K2 V2) where
  shrink :
    let refs2 := forRefs.shrink
    KVEquiv refs2.toKVRefs
  expand :
    let refs2 := forRefs.expand
    KVEquiv refs2.toKVRefs


end
end KVEquiv

attribute [simp] KVEquiv.rightInv KVEquiv.leftInv

/--
Owns the data representation `D`, the binary data type of primitive literals.

The only way to construct `D` is to parse a primitive literal in AST.
-/
structure HasData where
  D : DataU -- Binary Data type

/--
The syntax parameters, including the shared carrier used for free references.

It is deliberately left abstract to ward off unlawful construction:

- certified `C` receipts are obtained only through the runtime or build [KVEquiv.Lesser]
- the only way to construct `D` is to parse a primitive literal in AST
-/
structure Parameters extends HasData where
  C : KU -- shared carrier/receipt
  -- /--
  -- AST domain: dependent predicate that allow UIdRefs retrieval of values of guaranteed subtype
  -- AST of more specific domain can be used to constract AST of more general domain.
  -- - A typiccal use case of this is to construct compiletime AST (with domain covering both `Val` and `Typ`) from runtime AST (with domain only covering `Val`)
  -- -/
  -- dom : C -> Prop := λ _ => true --TODO: remove, useless now

namespace Parameters
section variable (Self : Parameters)

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
