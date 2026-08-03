import «Lp2lc».Active.Util

namespace Tests.FBoundExample

open Lp2lc.Active.Util
open FBound

/-- A simpleFBounde UIDs and values are both `Nat`. -/
def group : FBound Nat Nat where
  save := id
  load := id
  roundtrip := by
    intro value
    rfl

/-- First FBound instance: metadata is a `Bool` per value. -/
@[reducible] def boolBound : Aux group (λ _value => Bool) where
  Member := λ _id => Bool
  lookup := λ _id => none
  saveMember := λ bundle => bundle.snd
  loadMetadata := λ id2 => id2.snd

/-- Second FBound instance: metadata is `Unit` per value. -/
@[reducible] def unitBound : Aux group (λ _value => Unit) where
  Member := λ _id => Unit
  lookup := λ _id => none
  saveMember := λ bundle => bundle.snd
  loadMetadata := λ id2 => id2.snd

section roundtrip

example :
    boolBound.loadMetadata
      ⟨group.save 42, boolBound.saveMember ⟨42, true⟩⟩ = true := by
  rfl

example :
    unitBound.loadMetadata
      ⟨group.save 7, unitBound.saveMember ⟨7, ()⟩⟩ = () := by
  rfl

end roundtrip

section sharedGroup

example :
    boolBound.Member (group.save 1) ×
      unitBound.Member (group.save 1) :=
  ⟨boolBound.saveMember ⟨1, false⟩,
    unitBound.saveMember ⟨1, ()⟩⟩

end sharedGroup

end Tests.FBoundExample
