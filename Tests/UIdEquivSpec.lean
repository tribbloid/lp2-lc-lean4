import «Lp2lc».Active.Util

namespace Tests.UIdEquivSpec

open Lp2lc.Active.Util
@[reducible] def groupView : UIdRefs.{1} (λ _evidence => Nat) where
  UId := PSigma (λ _id : Nat => True)
  get := λ receipt => receipt.fst

@[reducible] def equalityView : UIdRefs.{1} (λ _evidence => Nat) where
  UId := PSigma (λ _id : Nat => 0 = 0)
  get := λ receipt => receipt.fst

abbrev EqOneValue := {value : Nat // value = 1}

@[reducible] def eqOneMetadataView :
    groupView.toKVRefs.Lesser
      (⟨Subtype.val, λ _left _right => Subtype.ext⟩ : EqOneValue ↪ Nat) where
  ev := λ receipt => receipt.fst = 1
  get := λ receipt => ⟨receipt.val.fst, receipt.property⟩
  equivariance := by
    intro receipt
    rfl

@[reducible] def unitMetadataView :
    groupView.toKVRefs.Lesser
      (⟨Prod.fst, λ _left _right h => Prod.ext h (Subsingleton.elim _ _)⟩ :
        Nat × Unit ↪ Nat) where
  ev := λ _receipt => True
  get := λ receipt => (groupView.get receipt.val, ())
  equivariance := by
    intro receipt
    rfl

section receipt

variable [eqOneMetadataCtx : KVEquiv eqOneMetadataView.toKVRefs]
variable [unitMetadataCtx : KVEquiv unitMetadataView.toKVRefs]

example :
    eqOneMetadataView.ev ⟨1, True.intro⟩ :=
  rfl

example :
    eqOneMetadataView.ev ⟨1, True.intro⟩ ∧
      unitMetadataView.ev ⟨1, True.intro⟩ :=
  ⟨rfl, True.intro⟩

example :
    eqOneMetadataView.ev ⟨1, True.intro⟩ → EqOneValue :=
  λ evidence => eqOneMetadataView.get ⟨⟨1, True.intro⟩, evidence⟩

example :
    unitMetadataView.ev ⟨1, True.intro⟩ → Nat × Unit :=
  λ evidence => unitMetadataView.get ⟨⟨1, True.intro⟩, evidence⟩

example (receipt : {uid // eqOneMetadataView.ev uid}) :
    (eqOneMetadataView.get receipt).val = groupView.get receipt.val := by
  exact eqOneMetadataView.equivariance receipt

example (receipt : {uid // unitMetadataView.ev uid}) :
    (unitMetadataView.get receipt).fst = groupView.get receipt.val := by
  exact unitMetadataView.equivariance receipt

example (value : EqOneValue) :
    eqOneMetadataView.get (eqOneMetadataCtx.inv value) = value := by
  simp

example (receipt : {uid // eqOneMetadataView.ev uid}) :
    eqOneMetadataCtx.inv (eqOneMetadataView.get receipt) = receipt := by
  simp

example (value : Nat × Unit) :
    unitMetadataView.get (unitMetadataCtx.inv value) = value := by
  simp

example (receipt : {uid // unitMetadataView.ev uid}) :
    unitMetadataCtx.inv (unitMetadataView.get receipt) = receipt := by
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
