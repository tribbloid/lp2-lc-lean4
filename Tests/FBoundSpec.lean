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
    boolMetadata.save ⟨1, true⟩ = boolMetadata.save ⟨1, false⟩ := by
  rfl

example :
    boolMetadata.save ⟨1, true⟩ = unitMetadata.save ⟨1, ()⟩ := by
  rfl

example :
    (boolMetadata.load
      (boolMetadata.save ⟨1, true⟩)
      (boolMetadata.saveMember ⟨1, true⟩)).fst = 1 := by
  rfl

example :
    (boolMetadata.load
      (boolMetadata.save ⟨1, true⟩)
      (boolMetadata.saveMember ⟨1, true⟩)).snd = true := by
  rfl

example :
    boolMetadata.lookup (unitMetadata.save ⟨1, ()⟩) = none := by
  rfl

end save

end Tests.FBoundSpec
