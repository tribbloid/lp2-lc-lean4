import «Lp2lc».Active.Util

namespace Tests.UIdEquivExample

open Lp2lc.Active.Util
open UIdEquiv

/-- A simple [UIdEquiv] whose UIds and values are both `Nat`. -/
def group : UIdEquiv Nat Nat where
  getUId := id
  inv := id
  leftInv := by
    intro value
    rfl
  rightInv := by
    intro id
    rfl

/-- First [UIdEquiv.Aux] instance: metadata is `value = 42`, evidence certifies the UId. -/
@[reducible] def eqBound : Aux group (λ value => value = 42) where
  Ev := λ id => group.inv id = 42
  getEv := λ bundle => bundle.snd
  invEv := λ id2 => id2.snd

/-- Second [UIdEquiv.Aux] instance: metadata is `Unit` per value. -/
@[reducible] def unitBound : Aux group (λ _value => Unit) where
  Ev := λ _id => True
  getEv := λ _bundle => True.intro
  invEv := λ _id2 => ()

section leftInv

example :
    eqBound.Ev (group.getUId 42) :=
  eqBound.getEv ⟨42, rfl⟩

example :
    eqBound.invEv
      ⟨group.getUId 42, eqBound.getEv ⟨42, rfl⟩⟩ = rfl := by
  rfl

example :
    unitBound.invEv
      ⟨group.getUId 7, unitBound.getEv ⟨7, ()⟩⟩ = () := by
  rfl

end leftInv

section sharedGroup

example :
    eqBound.Ev (group.getUId 42) ∧
      unitBound.Ev (group.getUId 7) :=
  ⟨eqBound.getEv ⟨42, rfl⟩,
    unitBound.getEv ⟨7, ()⟩⟩

end sharedGroup

end Tests.UIdEquivExample
