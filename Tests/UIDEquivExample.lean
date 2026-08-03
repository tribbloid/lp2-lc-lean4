import «Lp2lc».Active.Util

namespace Tests.UIDEquivExample

open Lp2lc.Active.Util
open UIDEquiv

/-- A simple [UIDEquiv] whose UIDs and values are both `Nat`. -/
def group : UIDEquiv Nat Nat where
  getUID := id
  inv := id
  leftInv := by
    intro value
    rfl
  rightInv := by
    intro id
    rfl

/-- First [UIDEquiv.Aux] instance: metadata is a `Bool` per value. -/
@[reducible] def boolBound : Aux group (λ _value => Bool) where
  Evidence := λ _id => Bool
  lookup := λ _id => none
  getEv := λ bundle => bundle.snd
  invEv := λ id2 => id2.snd

/-- Second [UIDEquiv.Aux] instance: metadata is `Unit` per value. -/
@[reducible] def unitBound : Aux group (λ _value => Unit) where
  Evidence := λ _id => Unit
  lookup := λ _id => none
  getEv := λ bundle => bundle.snd
  invEv := λ id2 => id2.snd

section leftInv

example :
    boolBound.invEv
      ⟨group.getUID 42, boolBound.getEv ⟨42, true⟩⟩ = true := by
  rfl

example :
    unitBound.invEv
      ⟨group.getUID 7, unitBound.getEv ⟨7, ()⟩⟩ = () := by
  rfl

end leftInv

section sharedGroup

example :
    boolBound.Evidence (group.getUID 1) ×
      unitBound.Evidence (group.getUID 1) :=
  ⟨boolBound.getEv ⟨1, false⟩,
    unitBound.getEv ⟨1, ()⟩⟩

end sharedGroup

end Tests.UIDEquivExample
