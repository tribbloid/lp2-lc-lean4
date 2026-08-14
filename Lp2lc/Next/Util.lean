import «Lp2lc».Active.Util

namespace Lp2lc.Next.Util

open Lp2lc.Active.Util


inductive Label
| typ
| trm
| val

class HasEv (UId : TIndex) where
  Ev : UId → Prop -- used to represent subtype of UId, implying extra condition

/-
TODO: I don't think subtyping is general enough

Math discovery relies on continuous supertyping (e.g. N -> Q), not subtyping. The design of UIdEquiv should be compatible to both directions
-/

/--
Receipt-indexed bridge between values and identifiers.

The value family is indexed by this bridge's evidence so recursive PHOAS
carriers can retain the receipt required by `get`.
-/
class UIdEquiv (UId : TIndex) (V : HasEv UId → Type) extends HasEv UId where
  get : (receipt : PSigma toHasEv.Ev) → V toHasEv
  inv : (value : V toHasEv) → PSigma toHasEv.Ev
  rightInv : ∀ (value : V toHasEv), get (inv value) = value
  leftInv : ∀ (receipt : PSigma toHasEv.Ev), inv (get receipt) = receipt

namespace UIdEquiv


/-- Attaches independently witnessed metadata to receipts from one outer bridge. -/
class Aux {UId : TIndex} {V : HasEv UId → Type}
    (outer : UIdEquiv UId V) (M : V outer.toHasEv → Sort u)
    extends HasEv (PSigma outer.toHasEv.Ev) where
  get : (receipt : PSigma toHasEv.Ev) → M (outer.get receipt.fst)
  inv : (bundle : PSigma M) → Ev (outer.inv bundle.fst)
end UIdEquiv

namespace Free

abbrev WithEv (self : Free) (augmentation : HasEv self.Carrier) : Free where
  Carrier := PSigma augmentation.Ev
  Data := self.Data

abbrev Fixpoint (self : Free) (V : Free → Type) :=
  UIdEquiv self.Carrier
    (λ evidence => V (WithEv self evidence))

/-- Constructs receipt-indexed fixpoint bridges for one free family. -/
class FixpointCtor (self : Free) where
  mkFixpoint (V : Free → Type) : Fixpoint self V

end Free

end Lp2lc.Next.Util
