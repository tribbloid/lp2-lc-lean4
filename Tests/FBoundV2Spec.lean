import «Lp2lc».Active.Util

namespace Tests.FBoundV2Spec

open Lp2lc.Active.Util

def group : FBoundGroup Nat Nat where
  save := id
  load := id
  roundtrip := by
    intro value
    rfl

@[reducible] def boolMetadata : FBoundV2 group (λ _value => Bool) where
  loadMetadata := λ _id => false

@[reducible] def unitMetadata : FBoundV2 group (λ _value => Unit) where
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

end Tests.FBoundV2Spec
