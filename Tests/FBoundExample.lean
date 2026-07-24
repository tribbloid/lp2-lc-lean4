import «Lp2lc».Active.Util

namespace Tests.FBoundExample

open Lp2lc.Active.Util

/-- A simple group where UIDs and values are both `Nat`. -/
def group : FBoundGroup Nat Nat where
  save := id
  load := id
  roundtrip := by
    intro value
    rfl

/-- First FBound instance: metadata is a `Bool` per value. -/
@[reducible] def boolBound : FBound group (λ _value => Bool) where
  loadMetadata := λ _id => true

/-- Second FBound instance: metadata is `Unit` per value. -/
@[reducible] def unitBound : FBound group (λ _value => Unit) where
  loadMetadata := λ _id => ()

section roundtrip

example : (boolBound.load (boolBound.save ⟨42, true⟩)).fst = 42 := by
  rfl

example : (unitBound.load (unitBound.save ⟨7, ()⟩)).fst = 7 := by
  rfl

end roundtrip

section sharedGroup

example :
    boolBound.save ⟨1, false⟩ = unitBound.save ⟨1, ()⟩ := by
  rfl

end sharedGroup

end Tests.FBoundExample
