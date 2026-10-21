import «Lp2lc».Active.STLC.Serial.Eval
import «Lp2lc».Active.STLC.UId.Eval
import «Tests».STLC.TrmDemo

namespace Tests.STLC.EvalSpec

open Lp2lc.Active.STLC Lp2lc.Active.Util
open Tests.STLC.Sanity

section eval

private def literalResult (result : Rec.Outcome (Option (Return ExeVal))) : Option String :=
  match result with
  | .yield (some (.some (.mk _ (.lit repr) _))) => some repr
  | _ => none

private def outerValue : ExeVal :=
  .mk 0 (.lit "outer") .empty
private def knownBindings : ExeBindings := (NatBindings.empty.set 0 outerValue).set 1 outerValue

example : literalResult (AST.eval Trm.primitiveIdFnOnFalse .empty 2) = some "false" := rfl
example : literalResult (AST.eval Trm.get1stOnTuple .empty 3) = some "false" := rfl
example : literalResult (AST.eval Trm.get2ndOnTuple .empty 3) = some "true" := rfl
example : literalResult (AST.eval Trm.FreeCapture.directRef knownBindings 1) = some "outer" := rfl
example : literalResult (AST.eval Trm.FreeCapture.capturedRefOnFalse knownBindings 2) = some "outer" := rfl
example : literalResult (AST.eval Trm.primitiveTrueFnOnFalse knownBindings 2) = some "true" := rfl
example : literalResult (AST.eval Trm.Malformed.WrongTypeIdFnOnFalse2 knownBindings 3) = some "false" := rfl

example : literalResult (AST.eval
    (.ref (P' := { B := String, I := IndexEncoding.Serial, index := ⟨1⟩ }) .only (.lower (.lower .same)) : Trm 3)
    (NatBindings.empty.set 1 outerValue) 1) = some "outer" := rfl

example : AST.eval Trm.vFalse .empty 0 = .outOfFuel := rfl
example : AST.eval Trm.Malformed.applyLit1 .empty 2 = .yield none := rfl
example : AST.eval (.ref Trm.FreeCapture.freeSlot .same : Trm 0) .empty 1 = .yield none := rfl
example : AST.eval (.apply Trm.vFalse Trm.primitiveIdFnOnFalse) .empty 2 = .outOfFuel := rfl
example : literalResult (AST.eval Trm.primitiveIdFnOnFalse knownBindings 2) = some "false" := rfl

end eval

namespace UId
open Root.Trm

section eval
variable (refs : UIdRefs) [build : BuildEnv refs]

private def literal : refs.base.Trm := .val (.lit "false")
private def identity : refs.base.Trm := .val (.fn .TLit (.mk (λ carrier => .ref carrier .same)))

example : eval (literal refs) 0 = .outOfFuel := rfl
example : eval (literal refs) 1 = .yield (some (.some (.lit "false"))) := rfl
example : eval (.apply (literal refs) (literal refs)) 1 = .outOfFuel := rfl
example : eval (.apply (literal refs) (literal refs)) 2 = .yield none := rfl
example : eval (.apply (literal refs) (.apply (identity refs) (literal refs))) 2 = .outOfFuel := rfl
example : eval (.apply (identity refs) (literal refs)) 1 = .outOfFuel := rfl
example : eval (.apply (identity refs) (literal refs)) 2 = .yield (some (.some (.lit "false"))) := by
  change eval (refs := refs) (.ref (build.uid2val (.lit "false")).val .same) 1 = _
  simp only [eval.eq_4, Root.mapRef.eq_1, BuildEnv.uid2val, KVEquiv.rightInv, Sum.getRight?, Option.map]

example : eval (refs := refs) (.ref (build.uid2val (.lit "outer")).val .same) 1 =
    .yield (some (.some (.lit "outer"))) := by
  simp only [eval.eq_4, Root.mapRef.eq_1, BuildEnv.uid2val, KVEquiv.rightInv, Sum.getRight?, Option.map]

example : eval (refs := refs) (.ref (build.uid2bothCtx.inv (.inl .TLit)) .same) 1 = .yield none := by
  simp only [eval.eq_4, Root.mapRef.eq_1, KVEquiv.rightInv, Sum.getRight?, Option.map]

end eval
end UId

end Tests.STLC.EvalSpec
