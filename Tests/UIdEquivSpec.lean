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

@[reducible] def eqOneMetadata : Lesser group (λ value => value = 1) where
  Ev := λ receipt => receipt.fst = 1
  inv := λ bundle => bundle.snd
  get := λ receipt => receipt.snd

@[reducible] def unitMetadata : Lesser group (λ _value => Unit) where
  Ev := λ _receipt => True
  inv := λ _bundle => True.intro
  get := λ _receipt => ()

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
  eqOneMetadata.inv ⟨1, rfl⟩

example :
    eqOneMetadata.Ev (group.inv 1) ∧
      unitMetadata.Ev (group.inv 1) :=
  ⟨eqOneMetadata.inv ⟨1, rfl⟩,
    unitMetadata.inv ⟨1, ()⟩⟩

example :
    eqOneMetadata.get
      ⟨group.inv 1, eqOneMetadata.inv ⟨1, rfl⟩⟩ = rfl := by
  rfl

example :
    unitMetadata.get
      ⟨group.inv 1, unitMetadata.inv ⟨1, ()⟩⟩ = () := by
  rfl

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
