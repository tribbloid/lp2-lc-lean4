import «Lp2lc».Active.STLC.Serial.Eval
import «Tests».STLC.TrmDemo

namespace Lp2lc.Active.STLC.AST

open Lp2lc.Active.Util Tests.STLC.Sanity

variable {n} (trm : Trm n) (fuel : Nat)

/-- Check the returned value and exact fuel cost. Invoke only as `trm.evalShouldYield fuel expected`. -/
private abbrev evalShouldYield (expected : Val) (bindings : ExeBindings := .empty) : Prop :=
  shouldYieldSyntax (trm.eval bindings) fuel (.some expected)

/-- Check runtime corruption and exact fuel cost. Invoke only as `trm.evalShouldCrash fuel`. -/
private abbrev evalShouldCrash (bindings : ExeBindings := .empty) : Prop :=
  shouldYieldSyntax (trm.eval bindings) fuel .corrupted

end Lp2lc.Active.STLC.AST

namespace Tests.STLC.Sanity.Trm

open Lp2lc.Active.Util Lp2lc.Active.STLC

section eval

#guard vFalse.asTrm.evalShouldYield 1 vFalse

#guard primitiveIdFn.evalShouldYield 1 Val.idFn

#guard primitiveIdFnOnFalse.evalShouldYield 2 vFalse

-- A nested identity is closed; a function returning its captured argument is not an identity.
#guard
  let trm : Trm := .apply get2nd vFalse
  trm.evalShouldYield 2 Val.idFn

#guard get1stOnTuple.evalShouldYield 3 vFalse

#guard get2ndOnTuple.evalShouldYield 3 vTrue

#guard primitiveTrueFnOnFalse.evalShouldYield 2 vTrue

#guard ¬ get1stOnFalse.evalShouldYield 2 Val.idFn

#guard higherOrderApplication.evalShouldYield 4 vFalse

#guard primitiveLiteralIdFnOnFalse.evalShouldYield 2 vFalse

#guard primitiveFirstFnOnTuple.evalShouldYield 3 vFalse

#guard Malformed.WrongTIn.eval.shouldFail 3

#guard Malformed.ContainWrongTIn.eval.shouldFail 4

#guard Malformed.applyLit1.eval.shouldFail 2

#guard Malformed.applyLit2.eval.shouldFail 3

#guard Malformed.applyLitToApplication.eval.shouldFail 3

#guard Malformed.wrongNestedTIn.eval.shouldFail 4

#guard Malformed.primitiveLiteralIdFnOnFn.eval.shouldFail 2

#guard Corrupted.corruptApplication.evalShouldCrash 2

#guard Corrupted.corruptedCallee.evalShouldCrash 3

#guard Corrupted.corruptedArgument.evalShouldCrash 3

#guard Corrupted.corruptedBody.evalShouldCrash 3

#guard Corrupted.illTypedPrimitiveResult.evalShouldCrash 4

#guard Corrupted.primitiveFnOnTuple.evalShouldCrash 3

end eval

end Tests.STLC.Sanity.Trm
