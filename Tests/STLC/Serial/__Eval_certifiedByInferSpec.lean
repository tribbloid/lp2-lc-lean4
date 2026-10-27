import «Lp2lc».Active.STLC.Serial.__Eval_certifiedByInfer
import «Tests».STLC.EvalDef

namespace Tests.STLC.EvalCertifiedByInferSpec

open Lp2lc.Active.STLC Lp2lc.Active.Util
open Tests.STLC.Sanity

section eval_certified

-- The test adapter infers first, independently of the exact evaluation budget.
private def erasedEval {n} (trm : Trm n) (bindings : ExeBindings := .empty)
    (inferFuel : Nat := 8) : RecOpt (Return ExeVal) :=
  match hInfer : trm.infer bindings inferFuel with
  | .yield (some _) => λ fuel =>
      (trm.eval_certified bindings hInfer fuel).map (λ result => some (result.map Subtype.val))
  | .yield none => λ _ => .yield none
  | .outOfFuel => λ _ => .outOfFuel

private def evalYields {n} (trm : Trm n) (fuel : Nat) (expected : ExeVal)
    (bindings : ExeBindings := .empty) : Bool :=
  match erasedEval trm bindings 8 fuel, erasedEval trm bindings 8 (fuel - 1) with
  | .yield (some (.some value)), .outOfFuel => closureSignature value == closureSignature expected
  | _, _ => false

private def outerValue : ExeVal := .mk 0 (.lit "outer") .empty
private def capturedBindings : ExeBindings := NatBindings.empty.set 0 outerValue
private def capturedClosure : ExeVal :=
  .mk 0 (.fn .TLit (.mk (λ _ => .ref Trm.FreeCapture.freeSlot (.lower .same)))) capturedBindings
private def callerBindings : ExeBindings := NatBindings.empty.set 0 capturedClosure
private def higherOrderId : Trm :=
  .val (.fn (.TFn .TLit .TLit) (.mk (λ fn => .ref fn .same)))
private def higherOrderApplication : Trm :=
  .apply (.apply higherOrderId Trm.primitiveIdFn) Trm.vFalse

private def corruptApplication (n : Nat := 0) : Trm n :=
  .apply (.val (.fnPrimitive (.TFn .TLit .TLit) .lit)) (.val (.lit "false"))

private def corruptsAt {n} (trm : Trm n) (fuel : Nat) : Bool :=
  match erasedEval trm .empty 8 fuel with
  | .yield (some .corrupted) => true
  | _ => false

-- Exact evaluation budgets include the one-less-budget exhaustion check.
#guard evalYields Trm.vFalse 1 falseValue
#guard evalYields Trm.primitiveIdFnOnFalse 2 falseValue
#guard evalYields Trm.get1stOnTuple 3 falseValue
#guard evalYields Trm.get2ndOnTuple 3 trueValue
#guard evalYields Trm.primitiveTrueFnOnFalse 2
  ⟨1, .lit bTrue, NatBindings.empty.set 1 falseValue⟩
#guard evalYields higherOrderApplication 3 falseValue
#guard evalYields Trm.FreeCapture.directRef 1 trueValue freeBindings
#guard evalYields Trm.FreeCapture.capturedRefOnFalse 2 trueValue freeBindings

#guard evalYields (.apply (.val (.fnPrimitive .TLit .lit)) Trm.vFalse) 2 falseValue
#guard evalYields Trm.primitiveFirstFnOnTuple 3 falseValue

#guard capturedPrimitiveCase (λ trm corrupted caller =>
  evalYields trm 5 trueValue caller && corruptsAt corrupted 3 &&
    match erasedEval corrupted .empty 8 2 with
    | .outOfFuel => true
    | _ => false)

#guard corruptsAt Trm.Malformed.primitiveFnOnTuple 3 &&
  match erasedEval Trm.Malformed.primitiveFnOnTuple .empty 8 2 with
  | .outOfFuel => true
  | _ => false

#guard corruptsAt corruptApplication 2
#guard corruptsAt corruptApplication 1000
#guard corruptsAt (.apply corruptApplication Trm.vTrue) 3
#guard corruptsAt (.apply higherOrderId corruptApplication) 3
#guard corruptsAt (.apply (.val (.fn .TLit (.mk (λ _ => corruptApplication 1)))) Trm.vFalse) 3

#guard match erasedEval corruptApplication .empty 2 1 with
  | .outOfFuel => true
  | _ => false

#guard
  let primitive : Val := .fnPrimitive .TLit
    (λ _ => .fn .TLit (.mk (λ _ => .apply (.val (.lit "bad")) (.val (.lit "bad")))))
  corruptsAt (.apply (.val primitive) Trm.vFalse) 4

-- The caller's slot zero holds a function; the applied closure captured a literal there.
#guard evalYields (.apply Trm.FreeCapture.directRef Trm.vTrue) 2 outerValue callerBindings

#guard (match erasedEval Trm.primitiveIdFn .empty 2 1 with
    | .yield (some (.some (.mk _ (.fn _ _) _))) => true
    | _ => false)

#guard (match erasedEval (.apply Trm.get1st Trm.vFalse) .empty 4 2 with
    | .yield (some (.some (.mk _ (.fn _ _) captured))) =>
      match captured 1 with
      | some (.mk _ (.lit repr) _) => repr == "false"
      | _ => false
    | _ => false)

#guard evalYields (.ref
    (P' := { B := String, I := IndexEncoding.Serial, index := ⟨1⟩ }) .only (.lower (.lower .same)) : Trm 3)
    1 outerValue (NatBindings.empty.set 1 outerValue)

#guard match Trm.vFalse.eval_certified .empty (inferFuel := 1) (typ := .TLit) rfl 0 with
  | .outOfFuel => true
  | _ => false

-- Rejected terms cannot supply the evaluator's inference-success premise, even when raw evaluation returns a value.
private def rejects {n} (trm : Trm n) : Bool :=
  match erasedEval trm .empty 8 0 with
  | .yield none => true
  | _ => false

#guard rejects Trm.Malformed.WrongTypeIdFnOnItself
#guard rejects Trm.Malformed.WrongTypeIdFnOnFalse2
#guard rejects Trm.Malformed.applyLit2
#guard rejects Trm.Malformed.applyLit1
#guard rejects (.apply (.val (.fnPrimitive .TLit .lit)) Trm.primitiveIdFn)
#check_failure Trm.Malformed.applyLit1.eval_certified .empty (inferFuel := 2) (typ := .TLit) rfl 2
#check_failure Trm.FreeCapture.directRef.eval_certified .empty (inferFuel := 1) (typ := .TLit) rfl 1
#check_failure Trm.Malformed.WrongTypeIdFnOnFalse2.eval_certified .empty (inferFuel := 4) (typ := .TLit) rfl 3
#check_failure AST.eval_certified (.apply Trm.vFalse Trm.primitiveIdFnOnFalse) .empty
  (inferFuel := 4) (typ := .TLit) rfl 2

#check_failure AST.CertifiedByInfer.inferReplace
#check_failure AST.CertifiedByInfer.inferMonotone
#check_failure AST.CertifiedByInfer.evalInternal
#check AST.CertifiedByInfer.Result

end eval_certified

end Tests.STLC.EvalCertifiedByInferSpec
