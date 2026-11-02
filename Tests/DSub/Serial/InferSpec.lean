import «Lp2lc».Active.DSub.Serial.Infer
import «Lp2lc».Active.DSub.Hash
import «Tests».DSub.TrmDemo

namespace Lp2lc.Active.Util.RecOpt

open Lp2lc.Active.DSub
open Lean (toJson)

/-- Compare DSub's closure-wrapped inference result with the expected DSub type syntax. -/
private abbrev shouldYieldType (computation : RecOpt CompilerTyp) (fuel : Nat) (expected : Typ) : Prop :=
  let offset (n index : Nat) := toJson (Int.ofNat index - Int.ofNat n)
  letI : BEq CompilerTyp :=
    ⟨λ first second =>
      match first.captured, second.captured with
      | .empty, .empty =>
        astBEq first.value second.value (offset first.n) toJson (offset second.n)
      | _, _ => false⟩
  computation.shouldYield fuel ⟨0, expected, .empty⟩

end Lp2lc.Active.Util.RecOpt

namespace Tests.DSub.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.DSub
open Lean (toJson)

section pure

#check_failure ((.ref IndexEncoding.SerialProxy.only .same : Pure) : Val)

#guard astToJson vFalse.asTrm toJson toJson ==
  .arr #["pure", .arr #["val", astToJson vFalse toJson toJson]]

end pure

section infer

private def fnBindings : ExeBindings := (NatBindings.empty.set 0 ⟨0, Val.idFn, .empty⟩).set 1 ⟨0, Val.idFn, .empty⟩

private def mixedBindings : ExeBindings := fnBindings.set 1 ⟨0, vTrue, .empty⟩

private def innerRef : Trm 1 := .pure (.ref (P' := { B := String, I := IndexEncoding.Serial, index := ⟨1⟩ }) .only .same)

#guard vFalse.asTrm.infer.shouldYieldType 1 .TLit

#guard vTrue.asTrm.infer.shouldYieldType 1 .TLit

#guard primitiveIdFn.infer.shouldYieldType 2 (.TFn .TLit (.mk (λ _ => .TLit)))

#guard primitiveIdFnOnFalse.infer.shouldYieldType 3 .TLit

#guard get1st.infer.shouldYieldType 3 (.TFn .TLit (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit))))))

#guard get2nd.infer.shouldYieldType 3 (.TFn .TLit (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit))))))

#guard get1stOnTuple.infer.shouldYieldType 5 .TLit

#guard get2ndOnTuple.infer.shouldYieldType 5 .TLit

#guard primitiveTrueFn.infer.shouldYieldType 2 (.TFn .TLit (.mk (λ _ => .TLit)))

#guard primitiveTrueFnOnFalse.infer.shouldYieldType 3 .TLit

#guard get1stOnFalse.infer.shouldYieldType 4 (.TFn .TLit (.mk (λ _ => .TLit)))

#guard higherOrderId.infer.shouldYieldType 2 (.TFn (.TFn .TLit (.mk (λ _ => .TLit))) (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit))))))

#guard higherOrderApplication.infer.shouldYieldType 4 .TLit

#guard primitiveLiteralIdFn.infer.shouldYieldType 1 (.TFn .TLit (.mk (λ _ => .TLit)))

#guard primitiveLiteralIdFnOnFalse.infer.shouldYieldType 2 .TLit

#guard primitiveFirstFnOnTuple.infer.shouldYieldType 3 .TLit

#guard Malformed.WrongTIn.infer.shouldFail 3

#guard Malformed.ContainWrongTIn.infer.shouldFail 4

#guard Malformed.applyLit1.infer.shouldFail 2

#guard Malformed.applyLit2.infer.shouldFail 4

#guard Malformed.applyLitToApplication.infer.shouldFail 4

#guard Malformed.wrongNestedTIn.infer.shouldFail 4

#guard Malformed.primitiveLiteralIdFnOnFn.infer.shouldFail 3

#guard Corrupted.corruptApplication.infer.shouldYieldType 2 (.TFn .TLit (.mk (λ _ => .TLit)))

#guard Corrupted.corruptedCallee.infer.shouldYieldType 3 .TLit

#guard Corrupted.corruptedArgument.infer.shouldYieldType 3 (.TFn .TLit (.mk (λ _ => .TLit)))

#guard Corrupted.corruptedBody.infer.shouldYieldType 4 (.TFn .TLit (.mk (λ _ => .TLit)))

#guard Corrupted.illTypedPrimitiveResult.infer.shouldYieldType 2 .TLit

#guard Corrupted.primitiveFnOnTuple.infer.shouldYieldType 3 .TLit

#guard (AST.infer (.pure (.val (.fn (.TFn .TLit (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit))))))
  (.mk (λ proxy => .pure (.ref proxy .same))))) : Trm 7)).shouldYieldType 2
  (.TFn (.TFn .TLit (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit)))))) (.mk (λ _ => (.TFn .TLit (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit)))))))))

#guard (primitiveIdFn.infer fnBindings).shouldYieldType 2 (.TFn .TLit (.mk (λ _ => .TLit)))

#guard (primitiveIdFn.infer mixedBindings).shouldYieldType 2 (.TFn .TLit (.mk (λ _ => .TLit)))

#guard (innerRef.infer mixedBindings).shouldYieldType 2 .TLit

#guard (AST.infer (.pure (.val (.fnPrimitive (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit))))) .lit)) : Trm)).shouldYieldType 1
  (.TFn .TLit (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit))))))

end infer

namespace InDSub

section infer

private def selectedReference {n} : Typ n :=
  .TSel (.ref IndexEncoding.SerialProxy.only .same)

private def capturedSelection (member : Typ) : CompilerTyp :=
  ⟨0, selectedReference, NatBindings.empty.set 0 ⟨0, member, .empty⟩⟩

private def importedSelection : Trm 1 :=
  .pure (.val (.typeDef selectedReference))

private def importedRuntime : ExeBindings :=
  let own : ExeBindings := NatBindings.empty.set 0 ⟨0, .typeDef .TLit, .empty⟩
  (NatBindings.empty.set 0 ⟨0, .typeDef Typ.idFn, .empty⟩).set 1 ⟨0, .typeDef selectedReference, own⟩

#guard boolType.infer.shouldYieldType 12 Typ.InDSub.boolType

#guard fnType.infer.shouldYieldType 12 Typ.InDSub.fnType

#guard boundedId.infer.shouldYieldType 12
  (.TFn Typ.InDSub.boundedMember (.mk (λ _ => Typ.InDSub.boundedMember)))

#guard boundedApplication.infer.shouldYieldType 12 Typ.InDSub.boundedMember

#guard selectedId.infer.shouldYieldType 12 Typ.idFn

#guard selectedApplication.infer.shouldYieldType 12 .TLit

#guard selectedFnId.infer.shouldYieldType 12 Typ.apply1stOn2ndFn

#guard selectedFnApplication.infer.shouldYieldType 12 .TLit

#guard [(dependentId, Typ.InDSub.dependentId), (dependentApplication, .TLit),
  (dependentType, Typ.InDSub.dependentType), (dependentTypeApplication, Typ.InDSub.boolType),
  (dependentFnTypeApplication, Typ.InDSub.fnType), (capturedId, Typ.InDSub.capturedId),
  (capturedApplication, .TLit), (capturedFnApplication, Typ.idFn),
  (boundedDependentId, Typ.InDSub.boundedDependentId), (boundedDependentApplication, .TLit)].all
    (λ (term, typ) => decide (term.infer.shouldYieldType 16 typ))

-- Identical source slots do not identify selections with different captured members.
#guard
  let literal : CompilerTyp := ⟨0, .TLit, .empty⟩
  let boolSelection := capturedSelection Typ.InDSub.boolType
  let bounded := capturedSelection Typ.InDSub.boundedMember
  let lowerBounded := capturedSelection Typ.InDSub.lowerBoundedMember
  let dependent : CompilerTyp := ⟨0, Typ.InDSub.dependentId, .empty⟩
  let reindexed : CompilerTyp := ⟨7, Typ.InDSub.dependentId, .empty⟩
  [(boolSelection, boolSelection, true), (boolSelection, capturedSelection Typ.InDSub.fnType, false),
    (bounded, literal, true), (literal, bounded, false),
    (literal, lowerBounded, true), (lowerBounded, literal, false),
    (dependent, reindexed, true), (reindexed, dependent, true)].all
      (λ (actual, upper, expected) =>
        match actual.subtype upper .empty 32 with
        | .yield accepted => accepted == expected
        | .outOfFuel => false)

-- An imported object's inner reference belongs to its own runtime, even when caller slots collide.
#guard [(⟨importedRuntime, .empty⟩ : CompilerBindings),
  ⟨importedRuntime, NatBindings.empty.set 0 ⟨0, Typ.InDSub.fnType, .empty⟩⟩].all
    (λ bindings => decide ((importedSelection.infer bindings).shouldYieldType 16 Typ.InDSub.boolType))

#guard [CompilerBindings.empty,
  ⟨NatBindings.empty.set 1 ⟨0, .lit bFalse, .empty⟩, .empty⟩].all
    (λ bindings => decide ((importedSelection.infer bindings).shouldFail 16))

#guard Malformed.applyTypeDef.infer.shouldFail 12

#guard Malformed.wrongMember.infer.shouldFail 12

#guard Malformed.wrongSelectedArgument.infer.shouldFail 12

#guard Malformed.wrongSelectedFnArgument.infer.shouldFail 12

#guard Malformed.wrongDependentArgument.infer.shouldFail 16

end infer

namespace Undecidable

section typeSelection

-- A function application is a term, not an operand of pure selection.
#check_failure (Pre.AST.TSel primitiveIdFnOnFalse)

end typeSelection

section infer

-- Full dependent-function subtyping accepts the direct narrowing that Scala rejects.
-- The identical narrowNegation2 fixture shares narrowNegation1's check.
#guard [narrowNegation1, narrow].all (λ term => decide (term.infer.shouldYieldType 16
  (.TFn (Negate .TTop) (.mk (λ _ => Negate .TLit)))))

-- Finite checkpoints observe the expanding query exhausting fuel; they do not prove divergence.
#guard [16, 128].all (λ fuel =>
  match expandingSubtyping.infer .empty fuel with
  | .outOfFuel => true
  | .yield _ => false)

end infer

end Undecidable

end InDSub

end Trm

end Sanity
