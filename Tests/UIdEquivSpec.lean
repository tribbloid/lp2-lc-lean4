import «Lp2lc».Active.Util

namespace Tests.UIdEquivSpec

open Lp2lc.Active.Util
open UIdEquiv

def group : UIdEquiv Nat Nat where
  inv := id
  get := id
  rightInv := by
    intro value
    rfl
  leftInv := by
    intro id
    rfl

@[reducible] def eqOneMetadata : Aux group (λ value => value = 1) where
  Ev := λ id => group.inv id = 1
  inv := λ bundle => bundle.snd
  get := λ id2 => id2.snd

@[reducible] def unitMetadata : Aux group (λ _value => Unit) where
  Ev := λ _id => True
  inv := λ _bundle => True.intro
  get := λ _id2 => ()

section inv

example :
    eqOneMetadata.Ev (group.inv 1) :=
  eqOneMetadata.inv ⟨1, rfl⟩

example :
    eqOneMetadata.Ev (group.inv 1) ∧
      unitMetadata.Ev (group.inv 1) :=
  ⟨eqOneMetadata.inv ⟨1, rfl⟩,
    unitMetadata.inv ⟨1, ()⟩⟩

example :
    group.get (group.inv 1) = 1 := by
  exact eqOneMetadata.rightInvValue ⟨1, rfl⟩

example :
    eqOneMetadata.get
      ⟨group.inv 1, eqOneMetadata.inv ⟨1, rfl⟩⟩ = rfl := by
  rfl

example :
    unitMetadata.get
      ⟨group.inv 1, unitMetadata.inv ⟨1, ()⟩⟩ = () := by
  rfl

end inv

end Tests.UIdEquivSpec
