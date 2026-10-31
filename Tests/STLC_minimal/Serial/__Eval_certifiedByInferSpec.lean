import «Lp2lc».Active.STLC_minimal.Serial.__Eval_certifiedByInfer
import «Tests».STLC_minimal.TrmDemo

namespace Lp2lc.Active.STLC_minimal.AST

open Lp2lc.Active.Util Tests.STLC_minimal.Sanity

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
  (match (erasedEval trm bindings) fuel with
  | .yield none => true
  | .yield (some (.some _)) =>
    panic! "The rejection test fixture is well-formed: inference and certified evaluation succeeded."
  | .yield (some .corrupted) =>
    panic! "Inference accepted a rejection fixture; certified evaluation reported allowed runtime corruption. Check the fixture and primitive contract."
  | .outOfFuel =>
    panic! "Inference or certified evaluation exhausted its fuel; rejection was not established. Soundness is inconclusive.") = true

end Lp2lc.Active.STLC_minimal.AST

namespace Tests.STLC_minimal.EvalCertifiedByInferSpec

open Lp2lc.Active.STLC_minimal Tests.STLC_minimal.Sanity Tests.STLC_minimal.Sanity.Trm

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

end Tests.STLC_minimal.EvalCertifiedByInferSpec
