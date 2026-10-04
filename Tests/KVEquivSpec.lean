import «Lp2lc».Active.Util

namespace Tests.UIdEquivSpec

open Lp2lc.Active.Util
@[reducible] def groupView : KVRefs (PSigma (λ _id : Nat => True)) Nat where
  get := λ receipt => receipt.fst

@[reducible] def equalityView : KVRefs (PSigma (λ _id : Nat => 0 = 0)) Nat where
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
    have _value : Nat := equalityView.get 1
  trivial

end rejection

end Tests.UIdEquivSpec
