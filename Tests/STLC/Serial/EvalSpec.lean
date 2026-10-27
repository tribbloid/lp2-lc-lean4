import «Lp2lc».Active.STLC.Serial.Eval
import «Tests».STLC.EvalDef

namespace Tests.STLC.Sanity.Trm

open Lp2lc.Active.Util Lp2lc.Active.STLC

section eval

-- TODO: name should be "Trm.evalShouldYields"
-- TODO: all invocations should use dot-notation



private def evalYields {n} (trm : Trm n) (fuel : Nat) (expected : ExeVal)
    (bindings : ExeBindings := .empty) : Bool :=
  match trm.eval bindings fuel, trm.eval bindings (fuel - 1) with
  | .yield (some (.some value)), .outOfFuel => closureSignature value == closureSignature expected
  | _, _ => false

#guard evalYields vFalse 1 falseValue

#guard evalYields primitiveIdFnOnFalse 2 falseValue

#guard evalYields get1stOnTuple 3 falseValue

#guard evalYields get2ndOnTuple 3 trueValue

-- TODO: evaluation of Malformed terms should always fail.
#guard evalYields Malformed.WrongTIn 2 ⟨0, Val.idFn, .empty⟩

#guard evalYields Malformed.ContainWrongTIn 3 falseValue

#guard Malformed.applyLit2.eval.shouldFail 3

#guard Malformed.applyLit1.eval.shouldFail 2

#guard evalYields primitiveTrueFnOnFalse 2
  ⟨1, .lit bTrue, NatBindings.empty.set 1 falseValue⟩

#guard evalYields FreeCapture.directRef 1 trueValue freeBindings

#guard evalYields FreeCapture.capturedRefOnFalse 2 trueValue freeBindings

-- TODO: all test case inputs should be included in the test fixture/demo
#guard evalYields (.apply (.val (.fnPrimitive .TLit .lit)) vFalse) 2 falseValue

#guard evalYields primitiveFirstFnOnTuple 3 falseValue

#guard capturedPrimitiveCase (λ trm corrupted caller =>
  evalYields trm 5 trueValue caller &&
    match AST.eval corrupted .empty 3, AST.eval corrupted .empty 2 with
    | .yield (some .corrupted), .outOfFuel => true
    | _, _ => false)

#guard match Malformed.primitiveFnOnTuple.eval .empty 3, Malformed.primitiveFnOnTuple.eval .empty 2 with
  | .yield (some .corrupted), .outOfFuel => true
  | _, _ => false

#guard (AST.eval (.apply (.val (.fnPrimitive .TLit .lit)) primitiveIdFn)).shouldFail 2

end eval

end Tests.STLC.Sanity.Trm
