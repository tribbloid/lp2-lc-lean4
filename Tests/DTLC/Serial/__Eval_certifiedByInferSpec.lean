import «Lp2lc».Active.DTLC.Serial.__Eval_certifiedByInfer
import «Tests».DTLC.TrmDemo

namespace Lp2lc.Active.DTLC.AST

open Lp2lc.Active.Util Tests.DTLC.Sanity

variable {n} (trm : Trm n) (fuel : Nat)

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

private abbrev evalShouldFail (bindings : ExeBindings := .empty) : Prop :=
  (match hInfer : trm.infer bindings 8 with
  | .yield none => true
  | .yield (some _) =>
    match trm.eval_certified bindings hInfer fuel with
    | .yield (.some _) => panic! "The rejection test fixture is well-formed: inference and certified evaluation succeeded."
    | .yield .corrupted =>
      panic! "Inference accepted a rejection fixture; certified evaluation reported allowed runtime corruption. Check the fixture and primitive contract."
    | .outOfFuel => panic! "Inference accepted a rejection fixture; certified evaluation exhausted its fuel. Soundness is inconclusive."
  | .outOfFuel => panic! "Inference exhausted its fuel; rejection was not established.") = true

end Lp2lc.Active.DTLC.AST

namespace Tests.DTLC.EvalCertifiedByInferSpec

open Lp2lc.Active.DTLC Tests.DTLC.Sanity Tests.DTLC.Sanity.Trm

section eval_certified

#guard vFalse.asTrm.evalShouldYield 1 vFalse

#guard primitiveIdFn.evalShouldYield 1 Val.idFn

#guard primitiveIdFnOnFalse.evalShouldYield 2 vFalse

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

end Tests.DTLC.EvalCertifiedByInferSpec
