import «Lp2lc».Active.Util

namespace Tests.FBoundSpec

open Lp2lc.Active.Util
open FBound

def group : FBound Nat Nat where
  save := id
  load := id
  roundtrip := by
    intro value
    rfl

@[reducible] def boolMetadata : Aux group (λ _value => Bool) where
  Member := λ _id => Bool
  lookup := λ _id => none
  saveMember := λ bundle => bundle.snd
  loadMetadata := λ _id member => member

@[reducible] def unitMetadata : Aux group (λ _value => Unit) where
  Member := λ _id => Unit
  lookup := λ _id => none
  saveMember := λ bundle => bundle.snd
  loadMetadata := λ _id member => member

section save

example :
    boolMetadata.Member (group.save 1) :=
  boolMetadata.saveMember ⟨1, true⟩

example :
    boolMetadata.Member (group.save 1) ×
      unitMetadata.Member (group.save 1) :=
  ⟨boolMetadata.saveMember ⟨1, true⟩,
    unitMetadata.saveMember ⟨1, ()⟩⟩

example :
    group.load (group.save 1) = 1 := by
  exact boolMetadata.roundtripValue ⟨1, true⟩

example :
    boolMetadata.loadMetadata
      (group.save 1)
      (boolMetadata.saveMember ⟨1, true⟩) = true := by
  rfl

example :
    boolMetadata.lookup (group.save 1) = none := by
  rfl

end save

end Tests.FBoundSpec
