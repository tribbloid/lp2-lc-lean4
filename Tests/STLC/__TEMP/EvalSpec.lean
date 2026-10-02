import «Lp2lc».Active.STLC.Serial.Eval
import «Tests».STLC.TrmDemo

namespace Tests.STLC.EvalSpec

open Lp2lc.Active.STLC Lp2lc.Active.Util
open Tests.STLC.Sanity

section eval

private def literalResult (result : Rec.Outcome (Option RuntimeValue)) : Option String :=
  match result with
  | .yield (some (RuntimeValue.mk (.lit repr) _ _)) => some repr
  | _ => none

private def outerValue : RuntimeValue :=
  .mk (.lit "outer" : AST 0 .val) (λ _ => 0) (λ _ => none)
private def rootIndices (_ref : CtxEmbedding.DeBruijn.TRef) : Nat := 0
private def knownBindings (index : Nat) : Option RuntimeValue :=
  if index = 0 then some outerValue else none
private def boolIndices (carrier : Bool) : Nat := if carrier then 17 else 23
private def sparseBindings (value : RuntimeValue) (index : Nat) : Option RuntimeValue :=
  if index = 17 then some value else none

example : literalResult (AST.eval Trm.primitiveIdFnOnFalse rootIndices (λ _ => none) 2) = some "false" := rfl
example : literalResult (AST.eval Trm.get1stOnTuple rootIndices (λ _ => none) 3) = some "false" := rfl
example : literalResult (AST.eval Trm.get2ndOnTuple rootIndices (λ _ => none) 3) = some "true" := rfl
example : literalResult (AST.eval Trm.FreeCapture.directRef
    (λ carrier => carrier.elim rootIndices (λ _ => 1)) knownBindings 1) = some "outer" := rfl
example : literalResult (AST.eval Trm.FreeCapture.capturedRefOnFalse rootIndices knownBindings 2) = some "outer" := rfl

example : AST.eval Trm.vFalse rootIndices (λ _ => none) 0 = .outOfFuel := rfl
example : AST.eval Trm.Malformed.primitiveApply rootIndices (λ _ => none) 2 = .yield none := rfl
example : AST.eval (.ref Trm.FreeCapture.freeSlot .same : Trm 0) rootIndices (λ _ => none) 1 = .yield none := rfl
example : AST.eval (.apply Trm.vFalse Trm.primitiveIdFnOnFalse) rootIndices (λ _ => none) 2 = .outOfFuel := rfl

example (value : RuntimeValue) :
    AST.eval (.ref true .same : AST 7 .trm Bool) boolIndices (sparseBindings value) 1 = .yield (some value) := rfl

example (value : RuntimeValue) :
    AST.eval (.ref false .same : AST 7 .trm Bool) boolIndices (sparseBindings value) 1 = .yield none := rfl

example : AST.eval (.apply
    (.val (.fn .TLit (.mk (λ _ => .ref (lower := CtxEmbedding.DeBruijn.toParameters.Next)
      (.inr .only) (.lower .same))))) Trm.vFalse : Trm 0)
    rootIndices knownBindings 2 = .yield none := rfl

end eval

end Tests.STLC.EvalSpec
