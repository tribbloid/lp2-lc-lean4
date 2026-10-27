import «Lp2lc».Active.STLC.Serial.Eval
import «Tests».STLC.EvalDef

namespace Tests.STLC.Sanity.Trm

open Lp2lc.Active.Util Lp2lc.Active.STLC

section eval

private abbrev _root_.Lp2lc.Active.STLC.Trm.evalShouldYields {n} (trm : Trm n) (fuel : Nat)
    (expected : Return ExeVal) (bindings : ExeBindings := .empty) : Prop :=
  (trm.eval bindings).shouldYields fuel expected

#guard vFalse.evalShouldYields 1 falseValue

#guard primitiveIdFn.evalShouldYields 1 idFnValue

#guard primitiveIdFnOnFalse.evalShouldYields 2 falseValue

#guard get1stOnFalse.evalShouldYields 2 get1stOnFalseValue

#guard get1stOnTuple.evalShouldYields 3 falseValue

#guard get2ndOnTuple.evalShouldYields 3 trueValue

#guard higherOrderApplication.evalShouldYields 4 falseValue

#guard Malformed.WrongTIn.eval.shouldFail 3

#guard Malformed.ContainWrongTIn.eval.shouldFail 4

#guard Malformed.wrongNestedTIn.eval.shouldFail 4

#guard Malformed.applyLit2.eval.shouldFail 3

#guard Malformed.applyLit1.eval.shouldFail 2

#guard Malformed.applyLitToApplication.eval.shouldFail 3

#guard primitiveTrueFnOnFalse.evalShouldYields 2 capturedTrueValue

#guard FreeVarCapture.directRef.evalShouldYields 1 trueValue freeBindings

#guard FreeVarCapture.directRef.eval.shouldFail 1

#guard FreeVarCapture.capturedRefOnFalse.evalShouldYields 2 trueValue freeBindings

#guard FreeVarCapture.directRefOnTrue.evalShouldYields 2 outerValue callerBindings

#guard FreeVarCapture.shiftedRef.evalShouldYields 1 outerValue shiftedBindings

#guard primitiveLiteralIdFnOnFalse.evalShouldYields 2 falseValue

#guard primitiveFirstFnOnTuple.evalShouldYields 3 falseValue

#guard FreeVarCapture.primitiveRefOnFalseTwice.evalShouldYields 5 trueValue capturedPrimitiveBindings

#guard Malformed.missingPrimitiveCapture.evalShouldYields 3 .corrupted

#guard Malformed.primitiveFnOnTuple.evalShouldYields 3 .corrupted

#guard Malformed.corruptApplication.evalShouldYields 2 .corrupted

#guard (Malformed.corruptApplication.eval .empty 1000).getOrElse none == some .corrupted

#guard Malformed.corruptedCallee.evalShouldYields 3 .corrupted

#guard Malformed.corruptedArgument.evalShouldYields 3 .corrupted

#guard Malformed.corruptedBody.evalShouldYields 3 .corrupted

#guard Malformed.illTypedPrimitiveResult.evalShouldYields 4 .corrupted

#guard Malformed.primitiveLiteralIdFnOnFn.eval.shouldFail 2

end eval

end Tests.STLC.Sanity.Trm
