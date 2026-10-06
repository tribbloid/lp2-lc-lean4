import «Lp2lc».Active.STLC.Serial.Eval
import «Tests».STLC.TrmDemo

namespace Tests.STLC.EvalSpec

open Lp2lc.Active.STLC Lp2lc.Active.Util
open Tests.STLC.Sanity

section eval

private def literalResult (result : Rec.Outcome (Option RuntimeValue)) : Option String :=
  match result with
  | .yield (some (RuntimeValue.mk _ (.lit repr) _)) => some repr
  | _ => none

private def outerValue : RuntimeValue :=
  .mk 0 (.lit "outer") (λ _ => none)
private def knownBindings : Nat → Option RuntimeValue :=
  λ _ => some outerValue

example : literalResult (AST.eval Trm.primitiveIdFnOnFalse (λ _ => none) 2) = some "false" := rfl
example : literalResult (AST.eval Trm.get1stOnTuple (λ _ => none) 3) = some "false" := rfl
example : literalResult (AST.eval Trm.get2ndOnTuple (λ _ => none) 3) = some "true" := rfl
example : literalResult (AST.eval Trm.FreeCapture.directRef knownBindings 1) = some "outer" := rfl
example : literalResult (AST.eval Trm.FreeCapture.capturedRefOnFalse knownBindings 2) = some "outer" := rfl
example : literalResult (AST.eval Trm.primitiveTrueFnOnFalse knownBindings 2) = some "true" := rfl
example : literalResult (AST.eval Trm.Malformed.idFnOnFalse2 knownBindings 3) = some "false" := rfl

example : literalResult (AST.eval
    (.ref (P' := { B := String, I := .Serial, index := 1 }) .only (.lower (.lower .same)) : Trm 3)
    (λ index => if index = 1 then some outerValue else none) 1) = some "outer" := rfl

example : AST.eval Trm.vFalse (λ _ => none) 0 = .outOfFuel := rfl
example : AST.eval Trm.Malformed.primitiveApply (λ _ => none) 2 = .yield none := rfl
example : AST.eval (.ref Trm.FreeCapture.freeSlot .same : Trm 0) (λ _ => none) 1 = .yield none := rfl
example : AST.eval (.apply Trm.vFalse Trm.primitiveIdFnOnFalse) (λ _ => none) 2 = .outOfFuel := rfl
example : literalResult (AST.eval Trm.primitiveIdFnOnFalse knownBindings 2) = some "false" := rfl

end eval

end Tests.STLC.EvalSpec
