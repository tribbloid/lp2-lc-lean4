import «Lp2lc».Active.Util

namespace Lp2lc.Next.Util

open Lp2lc.Active.Util

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
class UIdView (VK : UIdU → Type u) where
  UId : UIdU
  get : (uid : UId) → VK UId

/--
Full receipt-indexed bridge, extending `UIdView` with the reverse direction.

`inv` is the only way to obtain a UId: it requires a value, so a view alone
cannot mint receipts from new values.
-/
class UIdEquiv (VK : UIdU → Type u) extends UIdView VK where
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

/--
Owns the data representation `D`, the binary data type of primitive literals.

The only way to construct `D` is to parse a primitive literal in AST.
-/
class HasData where
  D : DataU -- Binary Data type

/--
the meaning of P in PHOAS, the collection of free type variables used in PHOAS bindings

They are deliberately left free to ward off unlawful construction:

- the only way to construct `C` is to get the UId of something already existing through [UIdEquiv]
- the only way to construct `D` is to parse a primitive literal in AST
-/
class Parameters extends HasData where
  C : UIdU -- Carrier type, AKA variable binding

namespace Free

/-- Receipt-indexed fixpoint bridge: its `UId` type is the receipt carrier, values are indexed by it. -/
abbrev Fixpoint (VK : UIdU → Type u) :=
  UIdEquiv VK

/-- Extends known receipt-indexed fixpoint bridges with new metadata views. -/
class FixpointExtender where
  mkLesser {VK : UIdU → Type u} (outer : Fixpoint VK) {M : VK outer.UId → Sort u} :
    UIdEquiv.Lesser outer M

end Free

end Lp2lc.Next.Util
