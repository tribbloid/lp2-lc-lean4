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

@[reducible] def boolMetadata : Aux group (λ _value => Bool) where
  Evidence := λ _id => Bool
  lookup := λ _id => none
  getEv := λ bundle => bundle.snd
  invEv := λ id2 => id2.snd

@[reducible] def unitMetadata : Aux group (λ _value => Unit) where
  Evidence := λ _id => Unit
  lookup := λ _id => none
  getEv := λ bundle => bundle.snd
  invEv := λ id2 => id2.snd

section getUID

example :
    boolMetadata.Evidence (group.getUID 1) :=
  boolMetadata.getEv ⟨1, true⟩

example :
    boolMetadata.Evidence (group.getUID 1) ×
      unitMetadata.Evidence (group.getUID 1) :=
  ⟨boolMetadata.getEv ⟨1, true⟩,
    unitMetadata.getEv ⟨1, ()⟩⟩

example :
    group.inv (group.getUID 1) = 1 := by
  exact boolMetadata.leftInvValue ⟨1, true⟩

example :
    boolMetadata.invEv
      ⟨group.getUID 1, boolMetadata.getEv ⟨1, true⟩⟩ = true := by
  rfl

example :
    boolMetadata.lookup (group.getUID 1) = none := by
  rfl

end getUID

end Tests.UIDEquivSpec
