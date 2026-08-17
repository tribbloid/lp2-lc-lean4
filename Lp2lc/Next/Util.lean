import «Lp2lc».Active.Util

namespace Lp2lc.Next.Util

open Lp2lc.Active.Util

universe u v

inductive Label
| typ
| trm
| val

/-
TODO: I don't think subtyping is general enough

Math discovery relies on continuous supertyping (e.g. N -> Q), not subtyping. The design of UIdEquiv should be compatible to both directions
-/

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

/-- Attaches independently witnessed metadata `M` to receipts from one outer bridge. -/
class Aux {VK : UIdU → Type u}
    (outer : UIdEquiv VK) (M : VK outer.UId → Sort v)
    extends HasEv outer.UId where
  get : (receipt : PSigma toHasEv.Ev) → M (outer.get receipt.fst)
  inv : (bundle : PSigma M) → Ev (outer.inv bundle.fst)

end UIdEquiv

namespace Free

/-- Receipt-indexed fixpoint bridge: its `UId` type is the receipt carrier, values are indexed by it. -/
abbrev Fixpoint (VK : UIdU → Type u) :=
  UIdEquiv VK

/-- Constructs receipt-indexed fixpoint bridges. -/
class FixpointCtor where
  mkFixpoint (VK : UIdU → Type u) : Fixpoint VK

end Free

end Lp2lc.Next.Util
