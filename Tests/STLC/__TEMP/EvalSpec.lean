import «Lp2lc».Active.STLC.Serial.Eval
import «Tests».STLC.TrmDemo

namespace Tests.STLC.EvalSpec

open Lp2lc.Active.STLC Lp2lc.Active.Util
open Tests.STLC.Sanity

section eval

private def literalResult (result : Rec.Outcome (Option RuntimeValue)) : Option String :=
  match result with
  | .yield (some (.lit repr)) => some repr
  | _ => none

private def outerValue : RuntimeValue :=
  .lit "outer"
private def knownBindings : Nat → Option RuntimeValue :=
  λ index => if index = 0 then some outerValue else none

example : literalResult (AST.eval Trm.primitiveIdFnOnFalse (λ _ => none) 2) = some "false" := rfl
example : literalResult (AST.eval Trm.get1stOnTuple (λ _ => none) 3) = some "false" := rfl
example : literalResult (AST.eval Trm.get2ndOnTuple (λ _ => none) 3) = some "true" := rfl
example : literalResult (AST.eval Trm.FreeCapture.directRef
    knownBindings 1) = some "outer" := rfl
example : literalResult (AST.eval Trm.FreeCapture.capturedRefOnFalse knownBindings 2) = some "outer" := rfl

example : AST.eval Trm.vFalse (λ _ => none) 0 = .outOfFuel := rfl
example : AST.eval Trm.Malformed.primitiveApply (λ _ => none) 2 = .yield none := rfl
example : AST.eval (.ref Trm.FreeCapture.freeSlot .same : Trm 0) (λ _ => none) 1 = .yield none := rfl
example : AST.eval (.apply Trm.vFalse Trm.primitiveIdFnOnFalse) (λ _ => none) 2 = .outOfFuel := rfl

end eval

end Tests.STLC.EvalSpec
