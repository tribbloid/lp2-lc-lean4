import «Lp2lc».Active.DTLC.Serial.Infer
import «Lp2lc».Active.DTLC.Hash
import «Tests».DTLC.TrmDemo

namespace Tests.DTLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.DTLC

section infer

local instance : BEq Typ :=
  ⟨λ first second => astBEq first second (λ _ => .null) (λ _ => .null)⟩

private def fnBindings : ExeBindings := (NatBindings.empty.set 0 ⟨0, Val.idFn, .empty⟩).set 1 ⟨0, Val.idFn, .empty⟩

private def mixedBindings : ExeBindings := fnBindings.set 1 ⟨0, vTrue, .empty⟩

private def innerRef : Trm 1 := .ref (P' := { B := String, I := IndexEncoding.Serial, index := ⟨1⟩ }) .only .same

#guard vFalse.asTrm.infer.shouldYield 1 .TLit

#guard vTrue.asTrm.infer.shouldYield 1 .TLit

#guard primitiveIdFn.infer.shouldYield 2 (.TFn .TLit (.mk (λ _ => .TLit)))

#guard primitiveIdFnOnFalse.infer.shouldYield 3 .TLit

#guard get1st.infer.shouldYield 3 (.TFn .TLit (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit))))))

#guard get2nd.infer.shouldYield 3 (.TFn .TLit (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit))))))

#guard get1stOnTuple.infer.shouldYield 5 .TLit

#guard get2ndOnTuple.infer.shouldYield 5 .TLit

#guard primitiveTrueFn.infer.shouldYield 2 (.TFn .TLit (.mk (λ _ => .TLit)))

#guard primitiveTrueFnOnFalse.infer.shouldYield 3 .TLit

#guard get1stOnFalse.infer.shouldYield 4 (.TFn .TLit (.mk (λ _ => .TLit)))

#guard higherOrderId.infer.shouldYield 2 (.TFn (.TFn .TLit (.mk (λ _ => .TLit))) (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit))))))

#guard higherOrderApplication.infer.shouldYield 4 .TLit

#guard primitiveLiteralIdFn.infer.shouldYield 1 (.TFn .TLit (.mk (λ _ => .TLit)))

#guard primitiveLiteralIdFnOnFalse.infer.shouldYield 2 .TLit

#guard primitiveFirstFnOnTuple.infer.shouldYield 3 .TLit

#guard Malformed.WrongTIn.infer.shouldFail 3

#guard Malformed.ContainWrongTIn.infer.shouldFail 4

#guard Malformed.applyLit1.infer.shouldFail 2

#guard Malformed.applyLit2.infer.shouldFail 4

#guard Malformed.applyLitToApplication.infer.shouldFail 4

#guard Malformed.wrongNestedTIn.infer.shouldFail 4

#guard Malformed.primitiveLiteralIdFnOnFn.infer.shouldFail 3

#guard Corrupted.corruptApplication.infer.shouldYield 2 (.TFn .TLit (.mk (λ _ => .TLit)))

#guard Corrupted.corruptedCallee.infer.shouldYield 3 .TLit

#guard Corrupted.corruptedArgument.infer.shouldYield 3 (.TFn .TLit (.mk (λ _ => .TLit)))

#guard Corrupted.corruptedBody.infer.shouldYield 4 (.TFn .TLit (.mk (λ _ => .TLit)))

#guard Corrupted.illTypedPrimitiveResult.infer.shouldYield 2 .TLit

#guard Corrupted.primitiveFnOnTuple.infer.shouldYield 3 .TLit

#guard (AST.infer (.val (.fn (.TFn .TLit (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit))))))
  (.mk (λ proxy => .ref proxy .same))) : Trm 7)).shouldYield 2
  (.TFn (.TFn .TLit (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit)))))) (.mk (λ _ => (.TFn .TLit (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit)))))))))

#guard (primitiveIdFn.infer fnBindings).shouldYield 2 (.TFn .TLit (.mk (λ _ => .TLit)))

#guard (primitiveIdFn.infer mixedBindings).shouldYield 2 (.TFn .TLit (.mk (λ _ => .TLit)))

#guard (innerRef.infer mixedBindings).shouldYield 2 .TLit

#guard (AST.infer (.val (.fnPrimitive (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit))))) .lit) : Trm)).shouldYield 1
  (.TFn .TLit (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit))))))

end infer

end Trm

end Sanity
