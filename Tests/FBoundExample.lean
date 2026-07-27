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
  roundtripId := by
    intro id
    rfl

/-- First FBound instance: metadata is a `Bool` per value. -/
@[reducible] def boolBound : Aux group (λ _value => Bool) where
  Evidence := λ _id => Bool
  lookup := λ _id => none
  saveMeta := λ bundle => bundle.snd
  loadMeta := λ id2 => id2.snd

/-- Second FBound instance: metadata is `Unit` per value. -/
@[reducible] def unitBound : Aux group (λ _value => Unit) where
  Evidence := λ _id => Unit
  lookup := λ _id => none
  saveMeta := λ bundle => bundle.snd
  loadMeta := λ id2 => id2.snd

section roundtrip

example :
    boolBound.loadMeta
      ⟨group.save 42, boolBound.saveMeta ⟨42, true⟩⟩ = true := by
  rfl

example :
    unitBound.loadMeta
      ⟨group.save 7, unitBound.saveMeta ⟨7, ()⟩⟩ = () := by
  rfl

end roundtrip

section sharedGroup

example :
    boolBound.Evidence (group.save 1) ×
      unitBound.Evidence (group.save 1) :=
  ⟨boolBound.saveMeta ⟨1, false⟩,
    unitBound.saveMeta ⟨1, ()⟩⟩

end sharedGroup

end Tests.FBoundExample
