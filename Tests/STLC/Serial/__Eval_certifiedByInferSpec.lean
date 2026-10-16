import «Lp2lc».Active.STLC.Serial.__Eval_certifiedByInfer
import «Tests».STLC.TrmDemo

namespace Tests.STLC.EvalCertifiedByInferSpec

open Lp2lc.Active.STLC Lp2lc.Active.Util
open Tests.STLC.Sanity

section eval_certified

-- The test adapter infers first, independently of the exact evaluation budget.
private def erasedEval {n} (trm : Trm n) (bindings : ExeBindings := .empty)
    (inferFuel : Nat := 8) : RecOpt ExeValue :=
  match hInfer : trm.infer bindings inferFuel with
  | .yield (some _) => λ fuel =>
      (trm.eval_certified bindings hInfer fuel).map (λ payload => some payload.val)
  | .yield none => λ _ => .yield none
  | .outOfFuel => λ _ => .outOfFuel

private def literalEval {n} (trm : Trm n) (bindings : ExeBindings := .empty) : RecOpt String := λ fuel =>
  (erasedEval trm bindings 8 fuel).map (Option.bind · (λ value =>
    match value.value with
    | .lit repr => some repr
    | .fn _ _ => none))

private def outerValue : ExeValue := .mk 0 (.lit "outer") .empty
private def capturedBindings : ExeBindings := NatBindings.empty.set 0 outerValue
private def capturedClosure : ExeValue :=
  .mk 0 (.fn .TLit (.mk (λ _ => .ref Trm.FreeCapture.freeSlot (.lower .same)))) capturedBindings
private def callerBindings : ExeBindings := NatBindings.empty.set 0 capturedClosure
private def higherOrderId : Trm :=
  .val (.fn (.TFn .TLit .TLit) (.mk (λ fn => .ref fn .same)))
private def higherOrderApplication : Trm :=
  .apply (.apply higherOrderId Trm.primitiveIdFn) Trm.vFalse

-- Exact evaluation budgets include the one-less-budget exhaustion check.
#guard (literalEval Trm.vFalse).shouldYields 1 "false"
#guard (literalEval Trm.primitiveIdFnOnFalse).shouldYields 2 "false"
#guard (literalEval Trm.get1stOnTuple).shouldYields 3 "false"
#guard (literalEval Trm.get2ndOnTuple).shouldYields 3 "true"
#guard (literalEval Trm.primitiveTrueFnOnFalse).shouldYields 2 "true"
#guard (literalEval higherOrderApplication).shouldYields 3 "false"
#guard (literalEval Trm.FreeCapture.directRef capturedBindings).shouldYields 1 "outer"
#guard (literalEval Trm.FreeCapture.capturedRefOnFalse capturedBindings).shouldYields 2 "outer"

-- The caller's slot zero holds a function; the applied closure captured a literal there.
#guard (literalEval (.apply Trm.FreeCapture.directRef Trm.vTrue) callerBindings).shouldYields 2 "outer"

#guard (match erasedEval Trm.primitiveIdFn .empty 2 1 with
    | .yield (some (.mk _ (.fn _ _) _)) => true
    | _ => false)

#guard (match erasedEval (.apply Trm.get1st Trm.vFalse) .empty 4 2 with
    | .yield (some (.mk _ (.fn _ _) captured)) =>
      match captured 1 with
      | some (.mk _ (.lit repr) _) => repr == "false"
      | _ => false
    | _ => false)

#guard (literalEval (.ref
    (P' := { B := String, I := IndexEncoding.Serial, index := ⟨1⟩ }) .only (.lower (.lower .same)) : Trm 3)
    (NatBindings.empty.set 1 outerValue)).shouldYields 1 "outer"
applyPrimitive
example : Trm.vFalse.eval_certified .empty (inferFuel := 1) (typ := .TLit) rfl 0 = .outOfFuel := rfl

-- Rejected terms cannot supply the evaluator's inference-success premise.
#guard Trm.Malformed.idFnOnFalse2.infer.shouldFail 4
#check_failure Trm.Malformed.primitiveApply.eval_certified .empty (inferFuel := 2) (typ := .TLit) rfl 2
#check_failure Trm.FreeCapture.directRef.eval_certified .empty (inferFuel := 1) (typ := .TLit) rfl 1
#check_failure Trm.Malformed.idFnOnFalse2.eval_certified .empty (inferFuel := 4) (typ := .TLit) rfl 3
#check_failure AST.eval_certified (.apply Trm.vFalse Trm.primitiveIdFnOnFalse) .empty
  (inferFuel := 4) (typ := .TLit) rfl 2

#check_failure AST.CertifiedByInfer.inferReplace
#check_failure AST.CertifiedByInfer.inferMonotone
#check_failure AST.CertifiedByInfer.evalInternal
#check AST.CertifiedByInfer.Result

end eval_certified

end Tests.STLC.EvalCertifiedByInferSpec
