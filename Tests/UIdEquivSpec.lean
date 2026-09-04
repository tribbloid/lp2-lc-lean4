import «Lp2lc».Active.Util

namespace Tests.UIdEquivSpec

open Lp2lc.Active.Util
open UIdEquiv

@[reducible] def groupView : UIdRefs.{1} (λ _evidence => Nat) where
  UId := PSigma (λ _id : Nat => True)
  get := λ receipt => receipt.fst

@[reducible] def equalityView : UIdRefs.{1} (λ _evidence => Nat) where
  UId := PSigma (λ _id : Nat => 0 = 0)
  get := λ receipt => receipt.fst

abbrev EqOneValue := {value : Nat // value = 1}

@[reducible] def eqOneMetadataView :
    UIdRefs.Lesser (V2 := EqOneValue) groupView Subtype.val where
  ev := λ receipt => receipt.fst = 1
  get := λ receipt => ⟨receipt.val.fst, receipt.property⟩
  equivariance := by
    intro receipt
    rfl

@[reducible] def eqOneMetadata :
    Lesser (V2 := EqOneValue) (base := groupView) Subtype.val where
  toLesser := eqOneMetadataView
  inv := λ value => ⟨⟨value.val, True.intro⟩, value.property⟩
  rightInv := by
    intro value
    rfl
  leftInv := by
    intro receipt
    apply Subtype.ext
    cases receipt.val with
    | mk _id evidence =>
      cases evidence
      rfl

@[reducible] def unitMetadataView :
    UIdRefs.Lesser (V2 := Nat × Unit) groupView Prod.fst where
  ev := λ _receipt => True
  get := λ receipt => (groupView.get receipt.val, ())
  equivariance := by
    intro receipt
    rfl

@[reducible] def unitMetadata :
    Lesser (V2 := Nat × Unit) (base := groupView) Prod.fst where
  toLesser := unitMetadataView
  inv := λ value => ⟨⟨value.fst, True.intro⟩, True.intro⟩
  rightInv := by
    intro value
    cases value with
    | mk value metadata =>
      cases metadata
      rfl
  leftInv := by
    intro receipt
    apply Subtype.ext
    cases receipt.val with
    | mk _id evidence =>
      cases evidence
      rfl

section receipt

example :
    eqOneMetadata.ev ⟨1, True.intro⟩ :=
  (eqOneMetadata.inv ⟨1, rfl⟩).property

example :
    eqOneMetadata.ev ⟨1, True.intro⟩ ∧
      unitMetadata.ev ⟨1, True.intro⟩ :=
  ⟨(eqOneMetadata.inv ⟨1, rfl⟩).property,
    (unitMetadata.inv (1, ())).property⟩

example :
    eqOneMetadata.ev ⟨1, True.intro⟩ → EqOneValue :=
  λ evidence => eqOneMetadata.get ⟨⟨1, True.intro⟩, evidence⟩

example :
    unitMetadata.ev ⟨1, True.intro⟩ → Nat × Unit :=
  λ evidence => unitMetadata.get ⟨⟨1, True.intro⟩, evidence⟩

example (receipt : {uid // eqOneMetadata.ev uid}) :
    (eqOneMetadata.get receipt).val = groupView.get receipt.val := by
  exact eqOneMetadata.equivariance receipt

example (receipt : {uid // eqOneMetadataView.ev uid}) :
    (eqOneMetadataView.get receipt).val = groupView.get receipt.val := by
  exact eqOneMetadataView.equivariance receipt

example (receipt : {uid // unitMetadata.ev uid}) :
    (unitMetadata.get receipt).fst = groupView.get receipt.val := by
  exact unitMetadata.equivariance receipt

example (receipt : {uid // unitMetadataView.ev uid}) :
    (unitMetadataView.get receipt).fst = groupView.get receipt.val := by
  exact unitMetadataView.equivariance receipt

example (value : EqOneValue) :
    eqOneMetadata.get (eqOneMetadata.inv value) = value := by
  simp

example (receipt : {uid // eqOneMetadata.ev uid}) :
    eqOneMetadata.inv (eqOneMetadata.get receipt) = receipt := by
  simp

example (value : Nat × Unit) :
    unitMetadata.get (unitMetadata.inv value) = value := by
  simp

example (receipt : {uid // unitMetadata.ev uid}) :
    unitMetadata.inv (unitMetadata.get receipt) = receipt := by
  simp

end receipt

section rejection

example : True := by
  fail_if_success
    have _receipt := groupView.inv 1
  trivial

example : True := by
  fail_if_success
    have _value : Nat := groupView.get 1
  trivial

example : True := by
  fail_if_success
    have _value : Nat := equalityView.get ⟨1, True.intro⟩
  trivial

end rejection

end Tests.UIdEquivSpec
