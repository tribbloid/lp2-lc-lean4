import «Lp2lc».Active.STLC.Eval
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
  .mk CtxEmbedding.DeBruijn.TRef (.lit "outer") (λ _ => none)
private def knownBindings : CtxEmbedding.DeBruijn.TRef → Option RuntimeValue :=
  λ _ => some outerValue

example : literalResult (AST.Trm.eval Trm.primitiveIdFnOnFalse (λ _ => none) 2) = some "false" := rfl
example : literalResult (AST.Trm.eval Trm.get1stOnTuple (λ _ => none) 3) = some "false" := rfl
example : literalResult (AST.Trm.eval Trm.get2ndOnTuple (λ _ => none) 3) = some "true" := rfl
example : literalResult (AST.Trm.eval Trm.FreeCapture.directRef
    (λ carrier => carrier.elim knownBindings (λ _ => none)) 1) = some "outer" := rfl
example : literalResult (AST.Trm.eval Trm.FreeCapture.capturedRefOnFalse knownBindings 2) = some "outer" := rfl

end eval

end Tests.STLC.EvalSpec
