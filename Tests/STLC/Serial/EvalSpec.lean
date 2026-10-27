import «Lp2lc».Active.STLC.Serial.Eval
import «Tests».STLC.TrmDemo

namespace Tests.STLC.Sanity.Trm

open Lp2lc.Active.Util Lp2lc.Active.STLC

section eval

private def evalYields {n} (trm : Trm n) (fuel : Nat) (expected : ExeVal)
    (bindings : ExeBindings := .empty) : Bool :=
  match trm.eval bindings fuel, trm.eval bindings (fuel - 1) with
  | .yield (some (.some value)), .outOfFuel => closureSignature value == closureSignature expected
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

#guard evalYields (.apply (.val (.fnPrimitive .TLit .lit)) vFalse) 2 falseValue

#guard evalYields (.apply
  (.apply (.val (.fnPrimitive (.TFn .TLit .TLit)
    (λ first => .fnPrimitive .TLit (λ _ => .lit first)))) vFalse) vTrue) 3 falseValue

#guard match FreeCapture.capturedRef with
  | .val value =>
    let primitive : Val := .fnPrimitive (.TFn .TLit .TLit) (λ _ => value)
    let caller := NatBindings.empty.set 0 (⟨0, primitive, freeBindings⟩ : ExeVal)
    evalYields (.apply (.apply FreeCapture.directRef vFalse) vFalse) 5 trueValue caller &&
      match AST.eval (.apply (.val primitive) vFalse) .empty 3,
          AST.eval (.apply (.val primitive) vFalse) .empty 2 with
      | .yield (some .corrupted), .outOfFuel => true
      | _, _ => false
  | _ => false

#guard
  let trm : Trm := .apply
    (.apply (.val (.fnPrimitive (.TFn .TLit .TLit)
      (λ _ => .fnPrimitive .TLit (λ _ => Val.idFn)))) vFalse) vTrue
  match trm.eval .empty 3, trm.eval .empty 2 with
  | .yield (some .corrupted), .outOfFuel => true
  | _, _ => false

#guard (AST.eval (.apply (.val (.fnPrimitive .TLit .lit)) primitiveIdFn)).shouldFail 2

end eval

end Tests.STLC.Sanity.Trm
