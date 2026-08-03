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

/-- First [UIDEquiv.Aux] instance: metadata is `value = 42`, evidence certifies the UID. -/
@[reducible] def eqBound : Aux group (λ value => value = 42) where
  Ev := λ id => group.inv id = 42
  lookup := λ _id => none
  getEv := λ bundle => bundle.snd
  invEv := λ id2 => id2.snd

/-- Second [UIDEquiv.Aux] instance: metadata is `Unit` per value. -/
@[reducible] def unitBound : Aux group (λ _value => Unit) where
  Ev := λ _id => True
  lookup := λ _id => none
  getEv := λ _bundle => True.intro
  invEv := λ _id2 => ()

section leftInv

example :
    eqBound.Ev (group.getUID 42) :=
  eqBound.getEv ⟨42, rfl⟩

example :
    eqBound.invEv
      ⟨group.getUID 42, eqBound.getEv ⟨42, rfl⟩⟩ = rfl := by
  rfl

example :
    unitBound.invEv
      ⟨group.getUID 7, unitBound.getEv ⟨7, ()⟩⟩ = () := by
  rfl

end leftInv

section sharedGroup

example :
    eqBound.Ev (group.getUID 42) ∧
      unitBound.Ev (group.getUID 7) :=
  ⟨eqBound.getEv ⟨42, rfl⟩,
    unitBound.getEv ⟨7, ()⟩⟩

end sharedGroup

end Tests.UIDEquivExample
