import «Lp2lc».Active.DSub.Serial.Infer
import «Lp2lc».Active.DSub.Hash
import «Tests».DSub.TrmDemo

namespace Lp2lc.Active.Util.RecOpt

open Lp2lc.Active.DSub

/-- Compare DSub's closure-wrapped inference result with the expected type syntax from DTLC. -/
private abbrev shouldYieldType (computation : RecOpt CompilerTyp) (fuel : Nat) (expected : Typ) : Prop :=
  letI : BEq CompilerTyp :=
    ⟨λ first second => astBEq first.value second.value (λ _ => .null) (λ _ => .null)⟩
  computation.shouldYield fuel ⟨0, expected, .empty⟩

end Lp2lc.Active.Util.RecOpt

namespace Tests.DSub.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.DSub

section infer

private def fnBindings : ExeBindings := (NatBindings.empty.set 0 ⟨0, Val.idFn, .empty⟩).set 1 ⟨0, Val.idFn, .empty⟩

private def mixedBindings : ExeBindings := fnBindings.set 1 ⟨0, vTrue, .empty⟩

private def innerRef : Trm 1 := .ref (P' := { B := String, I := IndexEncoding.Serial, index := ⟨1⟩ }) .only .same

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

#guard (AST.infer (.val (.fn (.TFn .TLit (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit))))))
  (.mk (λ proxy => .ref proxy .same))) : Trm 7)).shouldYieldType 2
  (.TFn (.TFn .TLit (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit)))))) (.mk (λ _ => (.TFn .TLit (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit)))))))))

#guard (primitiveIdFn.infer fnBindings).shouldYieldType 2 (.TFn .TLit (.mk (λ _ => .TLit)))

#guard (primitiveIdFn.infer mixedBindings).shouldYieldType 2 (.TFn .TLit (.mk (λ _ => .TLit)))

#guard (innerRef.infer mixedBindings).shouldYieldType 2 .TLit

#guard (AST.infer (.val (.fnPrimitive (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit))))) .lit) : Trm)).shouldYieldType 1
  (.TFn .TLit (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit))))))

end infer

end Trm

end Sanity
