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

@[reducible] def eqOneMetadataView : LesserView groupView (λ value => value = 1) where
  Ev := λ receipt => receipt.fst = 1
  get := λ receipt => receipt

@[reducible] def eqOneMetadata : Lesser (base := groupView) (λ value => value = 1) where
  toLesserView := eqOneMetadataView
  inv := by
    intro outer value tagged
    change groupView.get (outer.inv value) = 1
    rw [outer.rightInv]
    exact tagged
  rightInv := by
    intro _outer _value tagged
    exact proof_irrel_heq _ tagged
  leftInv := by
    intro _outer _uid receipt
    exact proof_irrel_heq _ receipt

@[reducible] def unitMetadataView : LesserView groupView (λ _value => Unit) where
  Ev := λ _receipt => True
  get := λ _receipt => ()

@[reducible] def unitMetadata : Lesser (base := groupView) (λ _value => Unit) where
  toLesserView := unitMetadataView
  inv := λ _outer _value _bundle => True.intro
  rightInv := by
    intro _outer _value tagged
    cases tagged
    rfl
  leftInv := by
    intro _outer _uid receipt
    exact proof_irrel_heq _ _

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
  eqOneMetadata.inv group rfl

example (outer : UIdEquiv groupView) :
    eqOneMetadata.Ev (outer.inv 1) :=
  eqOneMetadata.inv outer rfl

example :
    eqOneMetadata.Ev (group.inv 1) ∧
      unitMetadata.Ev (group.inv 1) :=
  ⟨eqOneMetadata.inv group rfl,
    unitMetadata.inv group ()⟩

example :
    eqOneMetadata.Ev (group.inv 1) → (1 = 1) :=
  λ h => eqOneMetadata.get h

example :
    unitMetadata.Ev (group.inv 1) → Unit :=
  λ h => unitMetadata.get h

example (outer : UIdEquiv groupView) {value : Nat} (tagged : value = 1) :
    HEq (eqOneMetadata.get (eqOneMetadata.inv outer tagged)) tagged := by
  simp

example (outer : UIdEquiv groupView) {uid : groupView.UId}
    (receipt : eqOneMetadata.Ev uid) :
    HEq (eqOneMetadata.inv outer (eqOneMetadata.get receipt)) receipt := by
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
