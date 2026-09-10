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
