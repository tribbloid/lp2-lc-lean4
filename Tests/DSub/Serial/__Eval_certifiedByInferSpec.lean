import «Lp2lc».Active.DSub.Serial.__Eval_certifiedByInfer
import «Tests».DSub.TrmDemo

namespace Lp2lc.Active.DSub.AST

open Lp2lc.Active.Util Tests.DSub.Sanity

variable {n} (trm : Trm n) (fuel : Nat)

private def erasedEval (bindings : ExeBindings := .empty) (inferFuel : Nat := 64) : RecOpt (Return ExeVal) :=
  match hInfer : trm.infer bindings inferFuel with
  | .yield (some _) => λ fuel =>
    (trm.eval_certified bindings hInfer fuel).map (λ result => some (result.map Subtype.val))
  | .yield none => λ _ => .yield none
  | .outOfFuel => λ _ => .outOfFuel

private abbrev evalShouldYield (expected : Val) (bindings : ExeBindings := .empty) : Prop :=
  shouldYieldSyntax (erasedEval trm bindings) fuel (.some expected)

private abbrev evalShouldCrash (bindings : ExeBindings := .empty) : Prop :=
  shouldYieldSyntax (erasedEval trm bindings) fuel .corrupted

private abbrev evalShouldFail (bindings : ExeBindings := .empty) : Prop :=
  (match hInfer : trm.infer bindings 64 with
  | .yield none => true
  | .yield (some _) =>
    match trm.eval_certified bindings hInfer fuel with
    | .yield (.some _) => panic! "The rejection test fixture is well-formed: inference and certified evaluation succeeded."
    | .yield .corrupted =>
      panic! "Inference accepted a rejection fixture; certified evaluation reported allowed runtime corruption. Check the fixture and primitive contract."
    | .outOfFuel => panic! "Inference accepted a rejection fixture; certified evaluation exhausted its fuel. Soundness is inconclusive."
  | .outOfFuel => panic! "Inference exhausted its fuel; rejection was not established.") = true

end Lp2lc.Active.DSub.AST

namespace Tests.DSub.EvalCertifiedByInferSpec

open Lp2lc.Active.DSub Lp2lc.Active.Util Tests.DSub.Sanity Tests.DSub.Sanity.Trm

section eval_certified

#guard vFalse.asTrm.evalShouldYield 1 vFalse

#guard primitiveIdFn.evalShouldYield 1 Val.idFn

#guard primitiveIdFnOnFalse.evalShouldYield 2 vFalse

#guard
  let trm : Trm := .apply get2nd vFalse
  trm.evalShouldYield 2 Val.idFn

#guard get1stOnTuple.evalShouldYield 3 vFalse

#guard get2ndOnTuple.evalShouldYield 3 vTrue

#guard primitiveTrueFnOnFalse.evalShouldYield 2 vTrue

#guard ¬ get1stOnFalse.evalShouldYield 2 Val.idFn

#guard higherOrderApplication.evalShouldYield 4 vFalse

#guard primitiveLiteralIdFnOnFalse.evalShouldYield 2 vFalse

#guard primitiveFirstFnOnTuple.evalShouldYield 3 vFalse

#guard Malformed.WrongTIn.evalShouldFail 3

#guard Malformed.ContainWrongTIn.evalShouldFail 4

#guard Malformed.applyLit1.evalShouldFail 2

#guard Malformed.applyLit2.evalShouldFail 3

#guard Malformed.applyLitToApplication.evalShouldFail 3

#guard Malformed.wrongNestedTIn.evalShouldFail 4

#guard Malformed.primitiveLiteralIdFnOnFn.evalShouldFail 2

#guard Corrupted.corruptApplication.evalShouldCrash 2

#guard Corrupted.corruptedCallee.evalShouldCrash 3

#guard Corrupted.corruptedArgument.evalShouldCrash 3

#guard Corrupted.corruptedBody.evalShouldCrash 3

#guard Corrupted.illTypedPrimitiveResult.evalShouldCrash 4

#guard Corrupted.primitiveFnOnTuple.evalShouldCrash 3

end eval_certified

namespace InDSub

open Tests.DSub.Sanity.Trm.InDSub

section eval_certified

private def aliasBindings (value : Val) : ExeBindings :=
  let reference : Val := .ref IndexEncoding.SerialProxy.only .same
  NatBindings.empty.set 0 ⟨0, reference, NatBindings.empty.set 0 ⟨0, value, .empty⟩⟩

private def aliasCallee : Trm :=
  .apply (.val (.ref IndexEncoding.SerialProxy.only .same)) vFalse

private def aliasArgument : Trm :=
  .apply primitiveIdFn (.val (.ref IndexEncoding.SerialProxy.only .same))

#guard boolType.evalShouldYield 16 (.typeDef .TLit)

#guard fnType.evalShouldYield 16 (.typeDef Typ.idFn)

#guard boundedApplication.evalShouldYield 16 (.typeDef .TLit)

#guard selectedApplication.evalShouldYield 16 vFalse

#guard selectedFnApplication.evalShouldYield 16 vTrue

#guard [dependentApplication, capturedApplication].all
  (λ term => decide (term.evalShouldYield 32 vFalse))

#guard boundedDependentApplication.evalShouldYield 32 vTrue

#guard capturedFnApplication.evalShouldYield 32 Val.idFn

-- Returned type definitions retain a reference in their source syntax and capture its member value.
#guard [dependentTypeApplication, dependentFnTypeApplication].all (λ term => decide
  (term.evalShouldYield 32 (.typeDef (.TSel (.ref IndexEncoding.SerialProxy.only .same)))))

#guard [(aliasCallee, aliasBindings Val.idFn), (aliasArgument, aliasBindings vFalse)].all
  (λ (term, bindings) => decide (term.evalShouldYield 32 vFalse bindings))

#guard
  match (aliasCallee.erasedEval (aliasBindings Val.idFn) 64) 2 with
  | .outOfFuel => true
  | .yield _ => false

#guard Malformed.applyTypeDef.evalShouldFail 16

#guard Malformed.wrongMember.evalShouldFail 16

#guard Malformed.wrongSelectedArgument.evalShouldFail 16

#guard Malformed.wrongSelectedFnArgument.evalShouldFail 16

#guard Malformed.wrongDependentArgument.evalShouldFail 32

end eval_certified

end InDSub

end Tests.DSub.EvalCertifiedByInferSpec
