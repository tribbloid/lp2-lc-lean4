
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

class Refs (K : KU) (V : Sort u) where
  get : (k : K) → V

namespace Refs

def ToUnit (K : KU) : Refs K Unit where
  get := λ _ => .unit

/-- Read-only access to a larger carrier, preserving the base receipt mapping. -/
class Greater {K V V2} (base : Refs K V) (upcastV : V ↪ V2)
    extends Refs K V2 where
  equivariance : ∀ (receipt : K), get receipt = upcastV (base.get receipt)

class HasEv (UId : KU) where
  ev : UId → Prop -- a subtype of UId with extra contract

/-- Read-only access to refined receipts compatible with a base view. -/
class Lesser {K V V2} (base : Refs K V) (upcastV : V2 ↪ V)
    extends HasEv K, Refs {uid // ev uid} V2 where
  equivariance : ∀ (receipt : {uid // ev uid}), upcastV (get receipt) = base.get receipt.val

end Refs

class HasUId where
  UId : KU

/--
Receipt-indexed bridge between values and identifiers. Read-only.

The value family is indexed by this bridge's evidence so recursive PHOAS
carriers can retain the receipt required by `get`.

type `V_` is deliberately a type constructor of `V`, without it V may be impossible to define due to cyclic references
-/
class UIdRefs (V_ : KU → Sort u) extends HasUId, Refs UId (V_ UId)

/--
Full receipt-indexed bridge, extending [UIdRefs] with the reverse direction.

`inv` is the only way to obtain a UId: it requires a value, so a view alone
cannot mint receipts from new values.

Not extendable, if you need to use the hypothetical `mkLesser`, use [RefEquiv].
-/
class _RefEquivProto {K V} (base : Refs K V) where
  private mk ::
  inv (value : V) : K
  rightInv : ∀ (value : V), base.get (inv value) = value
  leftInv : ∀ (receipt : K), inv (base.get receipt) = receipt

/--
Receipt-indexed fixpoint bridge: its `UId` type is the receipt carrier, values
are indexed by it.

Extends the inverse-only proto `_RefEquivProto` with `mkLesser`, which mints
refined [RefEquiv.Lesser] views for arbitrary upcasts.
-/
class RefEquiv {K V} (base : Refs K V) extends _RefEquivProto base where
  shrink {V2 : Sort u} (upcastV : V2 ↪ V) :
    PSigma (λ lesser : base.Lesser upcastV => _RefEquivProto lesser.toRefs)
  expand {V2 : Sort u} (upcastV : V ↪ V2) :
    PSigma (λ greater : base.Greater upcastV => _RefEquivProto greater.toRefs)

namespace RefEquiv

/-- Coerces a full bridge to the read-only view that it completes. -/
instance {K V} (base : Refs K V) : CoeOut (RefEquiv base) (Refs K V) where
  coe _self := base

end RefEquiv

attribute [simp] _RefEquivProto.rightInv _RefEquivProto.leftInv

/--
Owns the data representation `D`, the binary data type of primitive literals.

The only way to construct `D` is to parse a primitive literal in AST.
-/
class HasData where
  D : DataU -- Binary Data type

/--
the meaning of P in PHOAS, the shared carrier used in PHOAS bindings

It is deliberately left abstract to ward off unlawful construction:

- certified `C` receipts are obtained only through the runtime or build [RefEquiv.Lesser]
- the only way to construct `D` is to parse a primitive literal in AST
-/
class Parameters extends HasData where
  C : KU -- shared PHOAS/carrier UIdRefs/receipt
  /--
  AST domain: dependent predicate that allow UIdRefs retrieval of values of guaranteed subtype
  AST of more specific domain can be used to constract AST of more general domain.
  - A typiccal use case of this is to construct compiletime AST (with domain covering both `Val` and `Typ`) from runtime AST (with domain only covering `Val`)
  -/
  dom : C -> Prop := λ _ => true --TODO: remove, useless now

namespace Parameters
section variable (Self : Parameters)

def CC := {x // Self.dom x} -- certified carrier

/-- Builds a `Parameters` whose certified domain further restricts `Self.dom`,
so the refinement of `CC Self` holds by construction. -/
abbrev Lesser (ev : Self.C → Prop) : Parameters :=
  { D := Self.D, C := Self.C, dom := λ r => Self.dom r ∧ ev r }

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
