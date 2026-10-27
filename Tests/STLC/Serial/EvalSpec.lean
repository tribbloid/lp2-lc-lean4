import «Lp2lc».Active.STLC.Serial.Eval
import «Tests».STLC.TrmDemo

namespace Tests.STLC.Sanity.Trm

open Lp2lc.Active.Util Lp2lc.Active.STLC

section eval

private abbrev _root_.Lp2lc.Active.STLC.Trm.evalShouldYields {n} (trm : Trm n) (fuel : Nat)
    (expected : Return Val)
    (bindings : ExeBindings := .empty) : Prop :=
  returnsValue (trm.eval bindings) fuel expected

#guard vFalse.evalShouldYields 1 (.some falseValue)

#guard primitiveIdFn.evalShouldYields 1 (.some Val.idFn)

-- A nested identity is closed; a function returning its captured argument is not an identity.
#guard returnsValue (AST.eval (.apply get2nd vFalse : Trm)) 2 (.some Val.idFn)
#guard ¬ get1stOnFalse.evalShouldYields 2 (.some Val.idFn)

#guard primitiveIdFnOnFalse.evalShouldYields 2 (.some falseValue)

#guard get1stOnTuple.evalShouldYields 3 (.some falseValue)

#guard get2ndOnTuple.evalShouldYields 3 (.some trueValue)

#guard higherOrderApplication.evalShouldYields 4 (.some falseValue)

#guard Malformed.WrongTIn.eval.shouldFail 3

#guard Malformed.ContainWrongTIn.eval.shouldFail 4

#guard Malformed.wrongNestedTIn.eval.shouldFail 4

#guard Malformed.applyLit2.eval.shouldFail 3

#guard Malformed.applyLit1.eval.shouldFail 2

#guard Malformed.applyLitToApplication.eval.shouldFail 3

#guard primitiveTrueFnOnFalse.evalShouldYields 2 (.some trueValue)

#guard primitiveLiteralIdFnOnFalse.evalShouldYields 2 (.some falseValue)

#guard primitiveFirstFnOnTuple.evalShouldYields 3 (.some falseValue)

#guard Corrupted.primitiveFnOnTuple.evalShouldYields 3 .corrupted

#guard Corrupted.corruptApplication.evalShouldYields 2 .corrupted

#guard match Corrupted.corruptApplication.eval .empty 1000 with
  | .yield (some .corrupted) => true
  | _ => false

#guard Corrupted.corruptedCallee.evalShouldYields 3 .corrupted

#guard Corrupted.corruptedArgument.evalShouldYields 3 .corrupted

#guard Corrupted.corruptedBody.evalShouldYields 3 .corrupted

#guard Corrupted.illTypedPrimitiveResult.evalShouldYields 4 .corrupted

#guard Malformed.primitiveLiteralIdFnOnFn.eval.shouldFail 2

end eval

end Tests.STLC.Sanity.Trm
