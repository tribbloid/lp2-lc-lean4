import «Lp2lc».Active.STLC.Serial.__Eval_certifiedByInfer
import «Tests».STLC.TrmDemo

namespace Tests.STLC.EvalCertifiedByInferSpec


section eval_certified

-- TODO: these should be the same unit test as EvalSpec, the only difference is that they should test certified evaluation, why are they failing?
-- fix them by defining the missing functions

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

#guard Malformed.WrongTIn.evalShouldFail 3

#guard Malformed.ContainWrongTIn.evalShouldFail 4

#guard Malformed.applyLit1.evalShouldFail 2

#guard Malformed.applyLit2.evalShouldFail 3

#guard Malformed.applyLitToApplication.evalShouldFail 3

#guard Malformed.wrongNestedTIn.evalShouldFail 4

#guard Malformed.primitiveLiteralIdFnOnFn.evalShouldFail 2

#guard Corrupted.corruptApplication.evalShouldCrash 2

#guard Corrupted.corruptedCallee.evalShouldCrash 3

#guard Corrupted.corruptedArgument.evalShouldCrash 3

#guard Corrupted.corruptedBody.evalShouldCrash 3

#guard Corrupted.illTypedPrimitiveResult.evalShouldCrash 4

#guard Corrupted.primitiveFnOnTuple.evalShouldCrash 3

end eval_certified

end Tests.STLC.EvalCertifiedByInferSpec
