import «Lp2lc».Active.Util

namespace Tests.UIDEquivSpec

open Lp2lc.Active.Util
open UIDEquiv

def group : UIDEquiv Nat Nat where
  getUID := id
  inv := id
  leftInv := by
    intro value
    rfl
  rightInv := by
    intro id
    rfl

@[reducible] def eqOneMetadata : Aux group (λ value => value = 1) where
  Ev := λ id => group.inv id = 1
  lookup := λ _id => none
  getEv := λ bundle => bundle.snd
  invEv := λ id2 => id2.snd

@[reducible] def unitMetadata : Aux group (λ _value => Unit) where
  Ev := λ _id => True
  lookup := λ _id => none
  getEv := λ _bundle => True.intro
  invEv := λ _id2 => ()

section getUID

example :
    eqOneMetadata.Ev (group.getUID 1) :=
  eqOneMetadata.getEv ⟨1, rfl⟩

example :
    eqOneMetadata.Ev (group.getUID 1) ∧
      unitMetadata.Ev (group.getUID 1) :=
  ⟨eqOneMetadata.getEv ⟨1, rfl⟩,
    unitMetadata.getEv ⟨1, ()⟩⟩

example :
    group.inv (group.getUID 1) = 1 := by
  exact eqOneMetadata.leftInvValue ⟨1, rfl⟩

example :
    eqOneMetadata.invEv
      ⟨group.getUID 1, eqOneMetadata.getEv ⟨1, rfl⟩⟩ = rfl := by
  rfl

example :
    unitMetadata.invEv
      ⟨group.getUID 1, unitMetadata.getEv ⟨1, ()⟩⟩ = () := by
  rfl

example :
    eqOneMetadata.lookup (group.getUID 1) = none := by
  rfl

end getUID

end Tests.UIDEquivSpec
