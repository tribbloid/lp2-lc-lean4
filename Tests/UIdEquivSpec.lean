import «Lp2lc».Active.Util

namespace Tests.UIdEquivSpec

open Lp2lc.Active.Util
open UIdEquiv

@[reducible] def group : UIdEquiv.{0} (λ _evidence => Nat) where
  UId := PSigma (λ _id : Nat => True)
  inv := λ value => ⟨value, True.intro⟩
  get := λ receipt => receipt.fst
  rightInv := by
    intro value
    rfl
  leftInv := by
    intro receipt
    cases receipt with
    | mk _id evidence =>
      cases evidence
      rfl

@[reducible] def equalityGroup : UIdEquiv.{0} (λ _evidence => Nat) where
  UId := PSigma (λ _id : Nat => 0 = 0)
  inv := λ value => ⟨value, rfl⟩
  get := λ receipt => receipt.fst
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

example :
    group.get (group.inv 1) = 1 := by
  exact group.rightInv 1

example :
    group.inv (group.get (group.inv 1)) = group.inv 1 := by
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
    have _value : Nat := group.get 1
  trivial

example : True := by
  fail_if_success
    have _value : Nat := equalityGroup.get (group.inv 1)
  trivial

end rejection

end Tests.UIdEquivSpec
