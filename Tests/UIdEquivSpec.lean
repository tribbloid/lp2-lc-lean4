import «Lp2lc».Active.Util

namespace Tests.UIdEquivSpec

open Lp2lc.Active.Util
open UIdEquiv

def group : UIdEquiv Nat Nat where
  getUId := id
  inv := id
  leftInv := by
    intro value
    rfl
  rightInv := by
    intro id
    rfl

@[reducible] def eqOneMetadata : Aux group (λ value => value = 1) where
  Receipt := λ id => group.inv id = 1
  getEv := λ bundle => bundle.snd
  invEv := λ id2 => id2.snd

@[reducible] def unitMetadata : Aux group (λ _value => Unit) where
  Receipt := λ _id => True
  getEv := λ _bundle => True.intro
  invEv := λ _id2 => ()

section getUId

example :
    eqOneMetadata.Receipt (group.getUId 1) :=
  eqOneMetadata.getEv ⟨1, rfl⟩

example :
    eqOneMetadata.Receipt (group.getUId 1) ∧
      unitMetadata.Receipt (group.getUId 1) :=
  ⟨eqOneMetadata.getEv ⟨1, rfl⟩,
    unitMetadata.getEv ⟨1, ()⟩⟩

example :
    group.inv (group.getUId 1) = 1 := by
  exact eqOneMetadata.leftInvValue ⟨1, rfl⟩

example :
    eqOneMetadata.invEv
      ⟨group.getUId 1, eqOneMetadata.getEv ⟨1, rfl⟩⟩ = rfl := by
  rfl

example :
    unitMetadata.invEv
      ⟨group.getUId 1, unitMetadata.getEv ⟨1, ()⟩⟩ = () := by
  rfl

end getUId

end Tests.UIdEquivSpec
