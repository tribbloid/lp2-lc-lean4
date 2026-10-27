import «Lp2lc».Active.STLC.Serial.Eval
import «Tests».STLC.EvalDef

namespace Tests.STLC.Sanity.Trm

open Lp2lc.Active.Util Lp2lc.Active.STLC

section eval

private def _root_.Lp2lc.Active.STLC.Trm.evalShouldYields {n} (trm : Trm n) (fuel : Nat) (expected : ExeVal)
    (bindings : ExeBindings := .empty) : Bool :=
  match trm.eval bindings fuel, trm.eval bindings (fuel - 1) with
  | .yield (some (.some value)), .outOfFuel => closureSignature value == closureSignature expected
  | _, _ => false

#guard vFalse.evalShouldYields 1 falseValue

#guard primitiveIdFnOnFalse.evalShouldYields 2 falseValue

#guard get1stOnTuple.evalShouldYields 3 falseValue

#guard get2ndOnTuple.evalShouldYields 3 trueValue

#guard higherOrderApplication.evalShouldYields 4 falseValue

#guard Malformed.WrongTIn.eval.shouldFail 3

#guard Malformed.ContainWrongTIn.eval.shouldFail 4

#guard Malformed.wrongNestedTIn.eval.shouldFail 4

#guard Malformed.applyLit2.eval.shouldFail 3

#guard Malformed.applyLit1.eval.shouldFail 2

#guard primitiveTrueFnOnFalse.evalShouldYields 2 capturedTrueValue

#guard FreeCapture.directRef.evalShouldYields 1 trueValue freeBindings

#guard FreeCapture.capturedRefOnFalse.evalShouldYields 2 trueValue freeBindings

#guard primitiveLiteralIdFnOnFalse.evalShouldYields 2 falseValue

#guard primitiveFirstFnOnTuple.evalShouldYields 3 falseValue

#guard capturedPrimitiveCase (λ trm corrupted caller =>
  trm.evalShouldYields 5 trueValue caller &&
    match corrupted.eval .empty 3, corrupted.eval .empty 2 with
    | .yield (some .corrupted), .outOfFuel => true
    | _, _ => false)

#guard match Malformed.primitiveFnOnTuple.eval .empty 3, Malformed.primitiveFnOnTuple.eval .empty 2 with
  | .yield (some .corrupted), .outOfFuel => true
  | _, _ => false

#guard Malformed.primitiveLiteralIdFnOnFn.eval.shouldFail 2

end eval

end Tests.STLC.Sanity.Trm
