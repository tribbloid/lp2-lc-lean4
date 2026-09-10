
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

/--
Receipt-indexed bridge between values and PHOAS carriers. Read-only.

The value family is indexed by this bridge's evidence so recursive PHOAS
carriers can retain the receipt required by `get`.
-/
structure KVRefs (K : KU) (V : Sort u) where
  get : (k : K) → V

namespace KVRefs

def unit (K : KU) : KVRefs K Unit where
  get := λ _ => .unit

structure HasEv (UId : KU) where
  ev : UId → Prop -- a subtype of UId with extra contract

/-- Read-only access to a larger carrier, preserving the base receipt mapping. -/
structure Greater {K V V2} (base : KVRefs K V) (upcastV : V ↪ V2)
    extends KVRefs K V2 where
  equivariance : ∀ (receipt : K), get receipt = upcastV (base.get receipt)

/-- Read-only access to refined receipts compatible with a base view. -/
structure Lesser {K V V2} (base : KVRefs K V) (upcastV : V2 ↪ V)
    extends HasEv K, KVRefs {uid // ev uid} V2 where
  equivariance : ∀ (receipt : {uid // ev uid}), upcastV (get receipt) = base.get receipt.val

structure Adapter {K V} where
  shrink {V2 : Sort u} (v : KVRefs K V) (upcastV : V2 ↪ V) : v.Lesser upcastV -- converting a KVRefs to it's Lesser
  expand {V2 : Sort u} (v : KVRefs K V) (upcastV : V ↪ V2) : v.Greater upcastV -- converting a KVRefs to it's Greater

end KVRefs

structure HasUId where
  UId : KU

/--
Unlike [KVRefs], the key type `UId` is not shared with any other value type, so `get` cannot be abused to non-existing value.

type `V_` is deliberately a type constructor of `V`, without it V may be impossible to define due to cyclic references
-/
structure UIdRefs (V_ : KU → Sort u) extends HasUId, KVRefs UId (V_ UId)

/--
Full receipt-indexed bridge, extending [KVRefs] with the reverse direction.

`inv` is the only way to obtain a `K`: it requires a value, a view alone cannot mint receipts from new values.
-/
structure KVEquiv {K V} (base : KVRefs K V) where
  inv (value : V) : K
  rightInv : ∀ (value : V), base.get (inv value) = value
  leftInv : ∀ (receipt : K), inv (base.get receipt) = receipt

namespace KVEquiv

/-- Coerces a full bridge to the read-only view that it completes. -/
instance {K V} (base : KVRefs K V) : CoeOut (KVEquiv base) (KVRefs K V) where -- TODO: why do I need this?
  coe _self := base

structure Adapter {K V} where
  shrink {b} (v : KVEquiv b) (upcastV : V2 ↪ V) : KVEquiv (b.Lesser upcastV)
  expand {b} (v : KVEquiv b) (upcastV : V ↪ V2) : KVEquiv (b.Greater upcastV)

end KVEquiv

attribute [simp] KVEquiv.rightInv KVEquiv.leftInv

/--
Owns the data representation `D`, the binary data type of primitive literals.

The only way to construct `D` is to parse a primitive literal in AST.
-/
structure HasData where
  D : DataU -- Binary Data type

/--
the meaning of P in PHOAS, the shared carrier used in PHOAS bindings

It is deliberately left abstract to ward off unlawful construction:

- certified `C` receipts are obtained only through the runtime or build [KVEquiv.Lesser]
- the only way to construct `D` is to parse a primitive literal in AST
-/
class Parameters extends HasData where
  C : KU -- shared PHOAS/carrier UIdRefs/receipt
  -- /--
  -- AST domain: dependent predicate that allow UIdRefs retrieval of values of guaranteed subtype
  -- AST of more specific domain can be used to constract AST of more general domain.
  -- - A typiccal use case of this is to construct compiletime AST (with domain covering both `Val` and `Typ`) from runtime AST (with domain only covering `Val`)
  -- -/
  -- dom : C -> Prop := λ _ => true --TODO: remove, useless now
  adaptKVRefs : KVRefs.Adapter K V
  adaptKVEquiv : KVEquiv.Adapter K V

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
