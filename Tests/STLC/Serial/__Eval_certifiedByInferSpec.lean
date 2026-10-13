import «Lp2lc».Active.STLC.Serial.__Eval_certifiedByInfer
import «Tests».STLC.TrmDemo

namespace Tests.STLC.EvalCertifiedByInferSpec

open Lp2lc.Active.STLC Lp2lc.Active.Util
open Tests.STLC.Sanity

section eval_certified

private def erasedEval {n} (trm : Trm n) (bindings : ExeBindings := .empty) : RecOpt ExeValue :=
  λ fuel => (trm.eval_certified bindings fuel).result

private def literalEval {n} (trm : Trm n) (bindings : ExeBindings := .empty) : RecOpt String := λ fuel =>
  (erasedEval trm bindings fuel).map (Option.bind · (λ value =>
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
#guard (literalEval Trm.vFalse).shouldYieldsBool 1 "false"
#guard (literalEval Trm.primitiveIdFnOnFalse).shouldYieldsBool 2 "false"
#guard (literalEval Trm.get1stOnTuple).shouldYieldsBool 3 "false"
#guard (literalEval Trm.get2ndOnTuple).shouldYieldsBool 3 "true"
#guard (literalEval Trm.primitiveTrueFnOnFalse).shouldYieldsBool 2 "true"
#guard (literalEval higherOrderApplication).shouldYieldsBool 3 "false"
#guard (literalEval Trm.FreeCapture.directRef capturedBindings).shouldYieldsBool 1 "outer"
#guard (literalEval Trm.FreeCapture.capturedRefOnFalse capturedBindings).shouldYieldsBool 2 "outer"

-- The caller's slot zero holds a function; the applied closure captured a literal there.
#guard (literalEval (.apply Trm.FreeCapture.directRef Trm.vTrue) callerBindings).shouldYieldsBool 2 "outer"

#guard (match (Trm.primitiveIdFn.eval_certified .empty 1).result with
    | .yield (some (.mk _ (.fn _ _) _)) => true
    | _ => false)

#guard (match (AST.eval_certified (.apply Trm.get1st Trm.vFalse) .empty 2).result with
    | .yield (some (.mk _ (.fn _ _) captured)) =>
      match captured 1 with
      | some (.mk _ (.lit repr) _) => repr == "false"
      | _ => false
    | _ => false)

#guard (literalEval (.ref
    (P' := { B := String, I := IndexEncoding.Serial, index := ⟨1⟩ }) .only (.lower (.lower .same)) : Trm 3)
    (NatBindings.empty.set 1 outerValue)).shouldYieldsBool 1 "outer"

#guard (erasedEval Trm.Malformed.primitiveApply).shouldFailBool 2
#guard (erasedEval Trm.FreeCapture.directRef).shouldFailBool 1
example : (Trm.vFalse.eval_certified .empty 0).result = .outOfFuel := rfl
example : (AST.eval_certified (.apply Trm.vFalse Trm.primitiveIdFnOnFalse) .empty 2).result = .outOfFuel := rfl

-- Evaluation remains independent of inference acceptance, as in the original evaluator.
#guard Trm.Malformed.idFnOnFalse2.infer.shouldFailBool 4
#guard (literalEval Trm.Malformed.idFnOnFalse2).shouldYieldsBool 3 "false"

#check_failure AST.CertifiedByInfer.inferReplace
#check_failure AST.CertifiedByInfer.inferMonotone

end eval_certified

end Tests.STLC.EvalCertifiedByInferSpec
