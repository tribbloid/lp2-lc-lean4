import «Lp2lc».Active.STLC.Eval
import «Tests».STLC.TrmDemo

namespace Tests.STLC.EvalSpec

open Lp2lc.Active.STLC Lp2lc.Active.Util
open Tests.STLC.Sanity

section eval

private def literalResult {B TRefInc} (result : Rec.Outcome (Option (RuntimeValue B TRefInc))) : Option B :=
  match result with
  | .yield (some (RuntimeValue.mk _ (.lit repr) _)) => some repr
  | _ => none

private def outerValue : RuntimeValue String CtxEmbedding.DeBruijn.toParameters.TRefInc :=
  .mk CtxEmbedding.DeBruijn.TRef (.lit "outer") (λ _ => none)
private def knownBindings : CtxEmbedding.DeBruijn.TRef →
    Option (RuntimeValue String CtxEmbedding.DeBruijn.toParameters.TRefInc) :=
  λ _ => some outerValue

example : literalResult (AST.Trm.eval Trm.primitiveIdFnOnFalse (λ _ => none) 2) = some "false" := rfl
example : literalResult (AST.Trm.eval Trm.get1stOnTuple (λ _ => none) 3) = some "false" := rfl
example : literalResult (AST.Trm.eval Trm.get2ndOnTuple (λ _ => none) 3) = some "true" := rfl
example : literalResult (AST.Trm.eval Trm.FreeCapture.directRef
    (λ carrier => carrier.elim knownBindings (λ _ => none)) 1) = some "outer" := rfl
example : literalResult (AST.Trm.eval Trm.FreeCapture.capturedRefOnFalse knownBindings 2) = some "outer" := rfl

private abbrev optionalRefs : Parameters := { B := Nat, TRef := Bool, TRefInc := Option }

private instance : Parameters.RefBinding Option where
  fresh _ := none
  bind captured value carrier := carrier.elim (some value) captured

example : literalResult (AST.Trm.eval (P := optionalRefs)
    (.apply (.val (.fn .TLit (.mk (λ receipt => .ref receipt)))) (.val (.lit 7)))
    (λ _ => none) 2) = some 7 := rfl

example : literalResult (AST.Trm.eval (P := optionalRefs)
    (.apply (.val (.fn .TLit (.mk (λ _ => .ref (some true))))) (.val (.lit 7)))
    (λ carrier => if carrier then some (.mk Bool (.lit 23) (λ _ => none)) else none) 2) = some 23 := rfl

end eval

end Tests.STLC.EvalSpec
