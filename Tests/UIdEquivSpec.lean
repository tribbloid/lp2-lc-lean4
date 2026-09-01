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

@[reducible] def eqOneMetadataView : UIdView.Lesser groupView (λ value => value = 1) where
  Ev := λ receipt => receipt.fst = 1
  get := λ receipt => receipt

@[reducible] def eqOneMetadata : Lesser (base := groupView) (λ value => value = 1) where
  toLesser := eqOneMetadataView
  inv := by
    intro outer value tagged
    change groupView.get (outer.inv value) = 1
    rw [outer.rightInv]
    exact tagged
  rightInv := by
    intro _outer _value tagged
    exact proof_irrel_heq _ tagged

@[reducible] def unitMetadataView : UIdView.Lesser groupView (λ _value => Unit) where
  Ev := λ _receipt => True
  get := λ _receipt => ()

@[reducible] def unitMetadata : Lesser (base := groupView) (λ _value => Unit) where
  toLesser := unitMetadataView
  inv := λ _outer _value _bundle => True.intro
  rightInv := by
    intro _outer _value tagged
    cases tagged
    rfl

inductive WiderReceipt
  | base (receipt : groupView.UId)
  | extra

inductive WiderValue
  | base (value : Nat)
  | extra

@[reducible] def widerVK : UIdU → Type := λ _ => WiderValue

def upcastReceipt (receipt : groupView.UId) : WiderReceipt :=
  .base receipt

def upcastValue (value : Nat) : WiderValue :=
  .base value

@[reducible] def widerView : UIdView.Greater (VK2 := widerVK) groupView where
  UId := WiderReceipt
  get
    | .base receipt => .base (groupView.get receipt)
    | .extra => .extra
  upcastUId := upcastReceipt
  upcastV := upcastValue
  getUpcast _receipt := rfl

@[reducible] def widerGroup :
    Greater (base := groupView) widerVK where
  toGreater := widerView
  inv outer
    | .base value => .base (outer.inv value)
    | .extra => .extra
  rightInv outer value := by
    cases value with
    | base value => exact congrArg WiderValue.base (outer.rightInv value)
    | extra => rfl
  leftInv outer receipt := by
    cases receipt with
    | base receipt => exact congrArg WiderReceipt.base (outer.leftInv receipt)
    | extra => rfl

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

section greater

example (receipt : groupView.UId) :
    widerGroup.get (upcastReceipt receipt) = upcastValue (groupView.get receipt) := by
  exact widerGroup.getUpcast receipt

example : Function.Injective upcastReceipt := by
  intro left right equality
  cases equality
  rfl

example : Function.Injective upcastValue := by
  intro left right equality
  cases equality
  rfl

example (value : WiderValue) :
    widerGroup.get (widerGroup.inv group value) = value := by
  simp

example (receipt : WiderReceipt) :
    widerGroup.inv group (widerGroup.get receipt) = receipt := by
  simp

example : widerGroup.get (widerGroup.inv group .extra) = .extra := by
  rfl

example (outer : Extendable groupView) :
    Greater (base := groupView) widerVK :=
  outer.mkGreater widerVK

end greater

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
