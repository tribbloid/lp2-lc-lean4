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
  roundtripId := by
    intro id
    rfl

@[reducible] def boolMetadata : Aux group (λ _value => Bool) where
  Evidence := λ _id => Bool
  lookup := λ _id => none
  saveMeta := λ bundle => bundle.snd
  loadMeta := λ id2 => id2.snd

@[reducible] def unitMetadata : Aux group (λ _value => Unit) where
  Evidence := λ _id => Unit
  lookup := λ _id => none
  saveMeta := λ bundle => bundle.snd
  loadMeta := λ id2 => id2.snd

section save

example :
    boolMetadata.Evidence (group.save 1) :=
  boolMetadata.saveMeta ⟨1, true⟩

example :
    boolMetadata.Evidence (group.save 1) ×
      unitMetadata.Evidence (group.save 1) :=
  ⟨boolMetadata.saveMeta ⟨1, true⟩,
    unitMetadata.saveMeta ⟨1, ()⟩⟩

example :
    group.load (group.save 1) = 1 := by
  exact boolMetadata.roundtripValue ⟨1, true⟩

example :
    boolMetadata.loadMeta
      ⟨group.save 1, boolMetadata.saveMeta ⟨1, true⟩⟩ = true := by
  rfl

example :
    boolMetadata.lookup (group.save 1) = none := by
  rfl

end save

end Tests.FBoundSpec
