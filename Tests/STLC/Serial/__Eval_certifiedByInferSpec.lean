import «Lp2lc».Active.STLC.Serial.Eval
import «Lp2lc».Active.STLC.Serial.__Eval_certifiedByInfer
import «Tests».STLC.TrmDemo

namespace Lp2lc.Active.STLC.AST

open Lp2lc.Active.Util Tests.STLC.Sanity

variable {n} (trm : Trm n) (fuel : Nat)

-- Infer independently of evaluation fuel and erase only the returned value's certificate.
private def erasedEval (bindings : ExeBindings := .empty) (inferFuel : Nat := 8) : RecOpt (Return ExeVal) :=
  match hInfer : trm.infer bindings inferFuel with
  | .yield (some _) => λ fuel =>
    (trm.eval_certified bindings hInfer fuel).map (λ result => some (result.map Subtype.val))
  | .yield none => λ _ => .yield none
  | .outOfFuel => λ _ => .outOfFuel

private abbrev evalShouldYield (expected : Val) (bindings : ExeBindings := .empty) : Prop :=
  shouldYieldSyntax (erasedEval trm bindings) fuel (.some expected)

private abbrev evalShouldCrash (bindings : ExeBindings := .empty) : Prop :=
  shouldYieldSyntax (erasedEval trm bindings) fuel .corrupted

-- Rejected terms cannot supply the certified evaluator's premise; retain their exact runtime failure costs.
private abbrev evalShouldFail (bindings : ExeBindings := .empty) : Prop :=
  (match trm.infer bindings 8 with
  | .yield none => true
  | _ => false) = true ∧ (trm.eval bindings).shouldFail fuel

end Lp2lc.Active.STLC.AST

namespace Tests.STLC.EvalCertifiedByInferSpec

open Lp2lc.Active.STLC Tests.STLC.Sanity Tests.STLC.Sanity.Trm

section eval_certified

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
