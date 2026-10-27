import «Lp2lc».Active.STLC.Serial.__Eval_certifiedByInfer
import «Tests».STLC.TrmDemo

namespace Tests.STLC.EvalCertifiedByInferSpec

open Lp2lc.Active.STLC Lp2lc.Active.Util
open Tests.STLC.Sanity
open Tests.STLC.Sanity.Trm.Corrupted
  (corruptApplication corruptedCallee corruptedArgument corruptedBody illTypedPrimitiveResult)

section eval_certified

-- The test adapter infers first, independently of the exact evaluation budget.
private def erasedEval {n} (trm : Trm n) (bindings : ExeBindings := .empty)
    (inferFuel : Nat := 8) : RecOpt (Return ExeVal) :=
  match hInfer : trm.infer bindings inferFuel with
  | .yield (some _) => λ fuel =>
      (trm.eval_certified bindings hInfer fuel).map (λ result => some (result.map Subtype.val))
  | .yield none => λ _ => .yield none
  | .outOfFuel => λ _ => .outOfFuel

private abbrev evalYields {n} (trm : Trm n) (fuel : Nat) (expected : Return Val)
    (bindings : ExeBindings := .empty) : Prop :=
  returnsValue (erasedEval trm bindings) fuel expected

private def corruptsAt {n} (trm : Trm n) (fuel : Nat) : Bool :=
  match erasedEval trm .empty 8 fuel with
  | .yield (some .corrupted) => true
  | _ => false

-- Exact evaluation budgets include the one-less-budget exhaustion check.
#guard evalYields (n := 0) vFalse 1 (.some vFalse)
#guard evalYields Trm.primitiveIdFnOnFalse 2 (.some vFalse)
#guard evalYields Trm.get1stOnTuple 3 (.some vFalse)
#guard evalYields Trm.get2ndOnTuple 3 (.some vTrue)
#guard evalYields Trm.primitiveTrueFnOnFalse 2 (.some vTrue)
#guard evalYields Trm.higherOrderApplication 3 (.some vFalse)

#guard evalYields Trm.primitiveLiteralIdFnOnFalse 2 (.some vFalse)
#guard evalYields Trm.primitiveFirstFnOnTuple 3 (.some vFalse)

#guard evalYields Trm.Corrupted.primitiveFnOnTuple 3 .corrupted

#guard corruptsAt corruptApplication 2
#guard corruptsAt corruptApplication 1000
#guard corruptsAt corruptedCallee 3
#guard corruptsAt corruptedArgument 3
#guard corruptsAt corruptedBody 3

#guard match erasedEval corruptApplication .empty 2 1 with
  | .outOfFuel => true
  | _ => false

#guard corruptsAt illTypedPrimitiveResult 4

#guard evalYields Trm.primitiveIdFn 1 (.some Val.idFn)

#guard match vFalse.eval_certified (n := 0) .empty (inferFuel := 1) (typ := .TLit) rfl 0 with
  | .outOfFuel => true
  | _ => false

-- Rejected terms cannot supply the evaluator's inference-success premise, even when raw evaluation returns a value.
private def rejects {n} (trm : Trm n) : Bool :=
  match erasedEval trm .empty 8 0 with
  | .yield none => true
  | _ => false

#guard rejects Trm.Malformed.WrongTIn
#guard rejects Trm.Malformed.ContainWrongTIn
#guard rejects Trm.Malformed.applyLit2
#guard rejects Trm.Malformed.applyLit1
#guard rejects Trm.Malformed.primitiveLiteralIdFnOnFn
#check_failure Trm.Malformed.applyLit1.eval_certified .empty (inferFuel := 2) (typ := .TLit) rfl 2
#check_failure Trm.Malformed.ContainWrongTIn.eval_certified .empty (inferFuel := 4) (typ := .TLit) rfl 3
#check_failure Trm.Malformed.applyLitToApplication.eval_certified .empty
  (inferFuel := 4) (typ := .TLit) rfl 2

#check_failure AST.CertifiedByInfer.inferReplace
#check_failure AST.CertifiedByInfer.inferMonotone
#check_failure AST.CertifiedByInfer.evalInternal
#check AST.CertifiedByInfer.Result

end eval_certified

end Tests.STLC.EvalCertifiedByInferSpec
