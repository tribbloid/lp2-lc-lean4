import «Lp2lc».Active.STLC.Serial.__Eval_certifiedByInfer
import «Tests».STLC.EvalDef

namespace Tests.STLC.EvalCertifiedByInferSpec

open Lp2lc.Active.STLC Lp2lc.Active.Util
open Tests.STLC.Sanity
open Tests.STLC.Sanity.Trm.Malformed
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

private abbrev evalYields {n} (trm : Trm n) (fuel : Nat) (expected : Return ExeVal)
    (bindings : ExeBindings := .empty) : Prop :=
  (erasedEval trm bindings).shouldYields fuel expected

private def corruptsAt {n} (trm : Trm n) (fuel : Nat) : Bool :=
  match erasedEval trm .empty 8 fuel with
  | .yield (some .corrupted) => true
  | _ => false

-- Exact evaluation budgets include the one-less-budget exhaustion check.
#guard evalYields Trm.vFalse 1 falseValue
#guard evalYields Trm.primitiveIdFnOnFalse 2 falseValue
#guard evalYields Trm.get1stOnTuple 3 falseValue
#guard evalYields Trm.get2ndOnTuple 3 trueValue
#guard evalYields Trm.primitiveTrueFnOnFalse 2 capturedTrueValue
#guard evalYields Trm.higherOrderApplication 3 falseValue
#guard evalYields Trm.FreeVarCapture.directRef 1 trueValue freeBindings
#guard evalYields Trm.FreeVarCapture.capturedRefOnFalse 2 trueValue freeBindings

#guard evalYields Trm.primitiveLiteralIdFnOnFalse 2 falseValue
#guard evalYields Trm.primitiveFirstFnOnTuple 3 falseValue

#guard evalYields Trm.FreeVarCapture.primitiveRefOnFalseTwice 5 trueValue capturedPrimitiveBindings
#guard evalYields Trm.Malformed.missingPrimitiveCapture 3 .corrupted
#guard evalYields Trm.Malformed.primitiveFnOnTuple 3 .corrupted

#guard corruptsAt corruptApplication 2
#guard corruptsAt corruptApplication 1000
#guard corruptsAt corruptedCallee 3
#guard corruptsAt corruptedArgument 3
#guard corruptsAt corruptedBody 3

#guard match erasedEval corruptApplication .empty 2 1 with
  | .outOfFuel => true
  | _ => false

#guard corruptsAt illTypedPrimitiveResult 4

-- The caller's slot zero holds a function; the applied closure captured a literal there.
#guard evalYields Trm.FreeVarCapture.directRefOnTrue 2 outerValue callerBindings

#guard evalYields Trm.primitiveIdFn 1 idFnValue

#guard evalYields Trm.get1stOnFalse 2 get1stOnFalseValue

#guard evalYields Trm.FreeVarCapture.shiftedRef 1 outerValue shiftedBindings

#guard match Trm.vFalse.eval_certified .empty (inferFuel := 1) (typ := .TLit) rfl 0 with
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
#check_failure Trm.FreeVarCapture.directRef.eval_certified .empty (inferFuel := 1) (typ := .TLit) rfl 1
#check_failure Trm.Malformed.ContainWrongTIn.eval_certified .empty (inferFuel := 4) (typ := .TLit) rfl 3
#check_failure Trm.Malformed.applyLitToApplication.eval_certified .empty
  (inferFuel := 4) (typ := .TLit) rfl 2

#check_failure AST.CertifiedByInfer.inferReplace
#check_failure AST.CertifiedByInfer.inferMonotone
#check_failure AST.CertifiedByInfer.evalInternal
#check AST.CertifiedByInfer.Result

end eval_certified

end Tests.STLC.EvalCertifiedByInferSpec
