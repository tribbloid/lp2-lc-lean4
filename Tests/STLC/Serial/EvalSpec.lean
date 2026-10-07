import «Lp2lc».Active.STLC.Serial.Eval
import «Tests».STLC.TrmDemo

namespace Tests.STLC.EvalSpec

open Lp2lc.Active.STLC Lp2lc.Active.Util
open Tests.STLC.Sanity

section eval

private def literalResult (result : Rec.Outcome (Option ExeValue)) : Option String :=
  match result with
  | .yield (some (.mk _ (.lit repr) _)) => some repr
  | _ => none

private def outerValue : ExeValue :=
  .mk 0 (.lit "outer") .empty
private def knownBindings : ExeBindings := (Bindings.empty.set 0 outerValue).set 1 outerValue

example : literalResult (AST.eval Trm.primitiveIdFnOnFalse .empty 2) = some "false" := rfl
example : literalResult (AST.eval Trm.get1stOnTuple .empty 3) = some "false" := rfl
example : literalResult (AST.eval Trm.get2ndOnTuple .empty 3) = some "true" := rfl
example : literalResult (AST.eval Trm.FreeCapture.directRef knownBindings 1) = some "outer" := rfl
example : literalResult (AST.eval Trm.FreeCapture.capturedRefOnFalse knownBindings 2) = some "outer" := rfl
example : literalResult (AST.eval Trm.primitiveTrueFnOnFalse knownBindings 2) = some "true" := rfl
example : literalResult (AST.eval Trm.Malformed.idFnOnFalse2 knownBindings 3) = some "false" := rfl

example : literalResult (AST.eval
    (.ref (P' := { B := String, I := .Serial, index := 1 }) .only (.lower (.lower .same)) : Trm 3)
    (Bindings.empty.set 1 outerValue) 1) = some "outer" := rfl

example : AST.eval Trm.vFalse .empty 0 = .outOfFuel := rfl
example : AST.eval Trm.Malformed.primitiveApply .empty 2 = .yield none := rfl
example : AST.eval (.ref Trm.FreeCapture.freeSlot .same : Trm 0) .empty 1 = .yield none := rfl
example : AST.eval (.apply Trm.vFalse Trm.primitiveIdFnOnFalse) .empty 2 = .outOfFuel := rfl
example : literalResult (AST.eval Trm.primitiveIdFnOnFalse knownBindings 2) = some "false" := rfl

end eval

end Tests.STLC.EvalSpec
