import «Lp2lc».Active.Util

namespace Tests.UIdEquivExample

open Lp2lc.Active.Util
open UIdEquiv

/-- A simple [UIdEquiv] whose UIds and values are both `Nat`. -/
def group : UIdEquiv Nat Nat where
  inv := id
  get := id
  rightInv := by
    intro value
    rfl
  leftInv := by
    intro id
    rfl

/-- First [UIdEquiv.Aux] instance: metadata is `value = 42`, evidence certifies the UId. -/
@[reducible] def eqBound : Aux group (λ value => value = 42) where
  Ev := λ id => group.inv id = 42
  inv := λ bundle => bundle.snd
  get := λ id2 => id2.snd

/-- Second [UIdEquiv.Aux] instance: metadata is `Unit` per value. -/
@[reducible] def unitBound : Aux group (λ _value => Unit) where
  Ev := λ _id => True
  inv := λ _bundle => True.intro
  get := λ _id2 => ()

section rightInv

example :
    eqBound.Ev (group.inv 42) :=
  eqBound.inv ⟨42, rfl⟩

example :
    eqBound.get
      ⟨group.inv 42, eqBound.inv ⟨42, rfl⟩⟩ = rfl := by
  rfl

example :
    unitBound.get
      ⟨group.inv 7, unitBound.inv ⟨7, ()⟩⟩ = () := by
  rfl

end rightInv

section sharedGroup

example :
    eqBound.Ev (group.inv 42) ∧
      unitBound.Ev (group.inv 7) :=
  ⟨eqBound.inv ⟨42, rfl⟩,
    unitBound.inv ⟨7, ()⟩⟩

end sharedGroup

end Tests.UIdEquivExample
