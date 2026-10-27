import «Lp2lc».Active.STLC.Serial.Infer
import «Lp2lc».Active.STLC.Hash
import «Tests».STLC.TrmDemo

namespace Tests.STLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.STLC

section infer

local instance : BEq Typ :=
  ⟨λ first second => astBEq first second (λ _ => .null) (λ _ => .null)⟩

private def fnBindings : ExeBindings := (NatBindings.empty.set 0 ⟨0, Val.idFn, .empty⟩).set 1 ⟨0, Val.idFn, .empty⟩

private def mixedBindings : ExeBindings := fnBindings.set 1 ⟨0, vTrue, .empty⟩

private def innerRef : Trm 1 := .ref (P' := { B := String, I := IndexEncoding.Serial, index := ⟨1⟩ }) .only .same

#guard (vFalse.infer (n := 0)).shouldYields 1 .TLit

#guard (vTrue.infer (n := 0)).shouldYields 1 .TLit

#guard primitiveIdFn.infer.shouldYields 2 (.TFn .TLit .TLit)

#guard (AST.infer (.val (.fn (.TFn .TLit (.TFn .TLit .TLit))
  (.mk (λ proxy => .ref proxy .same))) : Trm 7)).shouldYields 2
  (.TFn (.TFn .TLit (.TFn .TLit .TLit)) (.TFn .TLit (.TFn .TLit .TLit)))

#guard primitiveIdFnOnFalse.infer.shouldYields 3 .TLit

#guard get1st.infer.shouldYields 3 (.TFn .TLit (.TFn .TLit .TLit))

#guard get2nd.infer.shouldYields 3 (.TFn .TLit (.TFn .TLit .TLit))

#guard get1stOnTuple.infer.shouldYields 5 .TLit

#guard get2ndOnTuple.infer.shouldYields 5 .TLit

#guard primitiveTrueFn.infer.shouldYields 2 (.TFn .TLit .TLit)

#guard primitiveTrueFnOnFalse.infer.shouldYields 3 .TLit

#guard (primitiveIdFn.infer fnBindings).shouldYields 2 (.TFn .TLit .TLit)

#guard (primitiveIdFn.infer mixedBindings).shouldYields 2 (.TFn .TLit .TLit)

#guard (innerRef.infer mixedBindings).shouldYields 2 .TLit

#guard Malformed.WrongTIn.infer.shouldFail 3

#guard Malformed.ContainWrongTIn.infer.shouldFail 4

#guard Malformed.applyLit2.infer.shouldFail 4

#guard Malformed.applyLit1.infer.shouldFail 2

#guard (AST.infer (.val (.fnPrimitive (.TFn .TLit .TLit) .lit) : Trm)).shouldYields 1
  (.TFn .TLit (.TFn .TLit .TLit))

#guard Malformed.primitiveLiteralIdFnOnFn.infer.shouldFail 3

end infer

end Trm

end Sanity
