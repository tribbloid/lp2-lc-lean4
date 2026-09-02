import «Lp2lc».Active.Util

namespace Tests.UIdEquivSpec

open Lp2lc.Active.Util
open UIdEquiv

@[reducible] def groupView : UIdView.{1} (λ _evidence => Nat) where
  UId := PSigma (λ _id : Nat => True)
  get := λ receipt => receipt.fst

@[reducible] def group : UIdEquiv groupView where
  inv := λ value => ⟨value, True.intro⟩
  rightInv := by
    intro value
    rfl
  leftInv := by
    intro receipt
    cases receipt with
    | mk _id evidence =>
      cases evidence
      rfl

@[reducible] def equalityView : UIdView.{1} (λ _evidence => Nat) where
  UId := PSigma (λ _id : Nat => 0 = 0)
  get := λ receipt => receipt.fst

@[reducible] def equalityGroup : UIdEquiv equalityView where
  inv := λ value => ⟨value, rfl⟩
  rightInv := by
    intro value
    rfl
  leftInv := by
    intro receipt
    cases receipt with
    | mk _id evidence =>
      cases evidence
      rfl

abbrev EqOneValue := {value : Nat // value = 1}

@[reducible] def eqOneMetadata :
    Lesser (V2 := EqOneValue) group Subtype.val where
  Ev := λ receipt => receipt.fst = 1
  get := λ receipt => ⟨receipt.val.fst, receipt.property⟩
  inv := λ value => ⟨group.inv value.val, value.property⟩
  equivariance := by
    intro receipt
    rfl
  rightInv := by
    intro value
    rfl

@[reducible] def unitMetadata :
    Lesser (V2 := Nat × Unit) group Prod.fst where
  Ev := λ _receipt => True
  get := λ receipt => (groupView.get receipt.val, ())
  inv := λ value => ⟨group.inv value.fst, True.intro⟩
  equivariance := by
    intro receipt
    rfl
  rightInv := by
    intro value
    cases value with
    | mk value metadata =>
      cases metadata
      rfl

section receipt

example : UIdView (λ _evidence => Nat) := group

example :
    (group : UIdView (λ _evidence => Nat)).get (group.inv 1) = 1 := by
  exact group.rightInv 1

example :
    group.inv ((group : UIdView (λ _evidence => Nat)).get (group.inv 1)) = group.inv 1 := by
  exact group.leftInv (group.inv 1)

example :
    eqOneMetadata.Ev (group.inv 1) :=
  (eqOneMetadata.inv ⟨1, rfl⟩).property

example :
    eqOneMetadata.Ev (group.inv 1) ∧
      unitMetadata.Ev (group.inv 1) :=
  ⟨(eqOneMetadata.inv ⟨1, rfl⟩).property,
    (unitMetadata.inv (1, ())).property⟩

example :
    eqOneMetadata.Ev (group.inv 1) → EqOneValue :=
  λ evidence => eqOneMetadata.get ⟨group.inv 1, evidence⟩

example :
    unitMetadata.Ev (group.inv 1) → Nat × Unit :=
  λ evidence => unitMetadata.get ⟨group.inv 1, evidence⟩

example (receipt : {uid // eqOneMetadata.Ev uid}) :
    (eqOneMetadata.get receipt).val = groupView.get receipt.val := by
  exact eqOneMetadata.equivariance receipt

example (receipt : {uid // unitMetadata.Ev uid}) :
    (unitMetadata.get receipt).fst = groupView.get receipt.val := by
  exact unitMetadata.equivariance receipt

example (value : EqOneValue) :
    eqOneMetadata.get (eqOneMetadata.inv value) = value := by
  simp

example (receipt : {uid // eqOneMetadata.Ev uid}) :
    eqOneMetadata.inv (eqOneMetadata.get receipt) = receipt := by
  simp

example (value : Nat × Unit) :
    unitMetadata.get (unitMetadata.inv value) = value := by
  simp

example (receipt : {uid // unitMetadata.Ev uid}) :
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
    have _value : Nat :=
      (equalityGroup : UIdView (λ _evidence => Nat)).get (group.inv 1)
  trivial

end rejection

end Tests.UIdEquivSpec
