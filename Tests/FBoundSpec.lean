import «Lp2lc».Active.Util

namespace Tests.FBoundSpec

open Lp2lc.Active.Util

def group : FBoundGroup Nat Nat where
  save := id
  load := id
  roundtrip := by
    intro value
    rfl

@[reducible] def boolMetadata : FBound group (λ _value => Bool) where
  loadMetadata := λ _id => false

@[reducible] def unitMetadata : FBound group (λ _value => Unit) where
  loadMetadata := λ _id => ()

section save

example :
    boolMetadata.save ⟨1, true⟩ = boolMetadata.save ⟨1, false⟩ := by
  rfl

example :
    boolMetadata.save ⟨1, true⟩ = unitMetadata.save ⟨1, ()⟩ := by
  rfl

example :
    (boolMetadata.load (boolMetadata.save ⟨1, true⟩)).fst = 1 := by
  rfl

end save

end Tests.FBoundSpec
