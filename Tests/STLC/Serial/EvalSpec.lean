import «Lp2lc».Active.STLC.Serial.Eval
import «Lp2lc».Active.STLC.Hash
import «Tests».STLC.TrmDemo

namespace Tests.STLC.Sanity.Trm

open Lp2lc.Active.Util Lp2lc.Active.STLC
open Lean (Json toJson)

section eval

private def signature (closure : ExeVal) : Json :=
  match closure with
  | .mk n value captured =>
    let rec bindings (entries : ExeBindings) : Json :=
      match entries with
      | .empty => .null
      | .set rest index value => .arr #[bindings rest, toJson index, signature value]
    .arr #[toJson n, astToJson value toJson toJson, bindings captured]
termination_by structural closure

private def evalYields {n} (trm : Trm n) (fuel : Nat) (expected : ExeVal)
    (bindings : ExeBindings := .empty) : Bool :=
  match trm.eval bindings fuel, trm.eval bindings (fuel - 1) with
  | .yield (some (.some value)), .outOfFuel => signature value == signature expected
  | _, _ => false

private def falseValue : ExeVal := ⟨0, .lit bFalse, .empty⟩
private def trueValue : ExeVal := ⟨0, .lit bTrue, .empty⟩
private def freeBindings : ExeBindings := NatBindings.empty.set 0 trueValue

#guard evalYields vFalse 1 falseValue

#guard evalYields primitiveIdFnOnFalse 2 falseValue

#guard evalYields get1stOnTuple 3 falseValue

#guard evalYields get2ndOnTuple 3 trueValue

#guard evalYields Malformed.WrongTypeIdFnOnItself 2 ⟨0, Val.idFn, .empty⟩

#guard evalYields Malformed.WrongTypeIdFnOnFalse2 3 falseValue

#guard Malformed.applyLit2.eval.shouldFail 3

#guard Malformed.applyLit1.eval.shouldFail 2

#guard evalYields primitiveTrueFnOnFalse 2
  ⟨1, .lit bTrue, NatBindings.empty.set 1 falseValue⟩

#guard evalYields FreeCapture.directRef 1 trueValue freeBindings

#guard evalYields FreeCapture.capturedRefOnFalse 2 trueValue freeBindings

end eval

end Tests.STLC.Sanity.Trm
