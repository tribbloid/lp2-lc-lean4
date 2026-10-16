import «Lp2lc».Active.STLC.Serial.__Infer
import «Lp2lc».Active.STLC.Serial.Eval
import «Lp2lc».Active.STLC.Hash
import «Tests».STLC.TrmDemo

namespace Tests.STLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.STLC

section infer

local instance : BEq Typ :=
  ⟨λ first second => astBEq first second (λ _ => .null) (λ _ => .null)⟩

private def literalValue : ExeValue := .mk 0 (.lit bTrue) .empty

private def fnValue : ExeValue :=
  .mk 0 (.fn .TLit (.mk (λ proxy => .ref proxy .same))) .empty

private def literalBindings : ExeBindings := NatBindings.empty.set 0 literalValue

private def fnBindings : ExeBindings := (NatBindings.empty.set 0 fnValue).set 1 fnValue

private def mixedBindings : ExeBindings := fnBindings.set 1 literalValue

private def innerRef : Trm 1 := .ref (P' := { B := String, I := IndexEncoding.Serial, index := ⟨1⟩ }) .only .same

#guard vFalse.infer.shouldYields 1 .TLit

#guard vTrue.infer.shouldYields 1 .TLit

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

#guard TypeHinted.hintedFalse.infer.shouldYields 1 .TLit

#guard TypeHinted.hintedIdFn.infer.shouldYields 2 (.TFn .TLit .TLit)

#guard TypeHinted.hintedIdFnOnFalse.infer.shouldYields 3 .TLit

#guard (FreeCapture.directRef.infer literalBindings).shouldYields 2 .TLit

#guard (AST.infer (.ref FreeCapture.freeSlot .same : Trm 0) literalBindings).shouldYields 2 .TLit

#guard (FreeCapture.directRef.infer fnBindings).shouldYields 3 (.TFn .TLit .TLit)

#guard (FreeCapture.capturedRef.infer fnBindings).shouldYields 4
  (.TFn .TLit (.TFn .TLit .TLit))

#guard (FreeCapture.capturedRefOnFalse.infer fnBindings).shouldYields 5 (.TFn .TLit .TLit)

#guard (primitiveIdFn.infer fnBindings).shouldYields 2 (.TFn .TLit .TLit)

#guard (primitiveIdFn.infer mixedBindings).shouldYields 2 (.TFn .TLit .TLit)

#guard (FreeCapture.directRef.infer mixedBindings).shouldYields 3 (.TFn .TLit .TLit)

#guard (innerRef.infer mixedBindings).shouldYields 2 .TLit

#guard (AST.infer (.apply FreeCapture.directRef primitiveIdFn) fnBindings).shouldFail 4

#guard match FreeCapture.capturedRef.eval (NatBindings.empty.set 0 literalValue) 1 with
  | .yield (some closure) =>
    let bindings := mixedBindings.set 1 closure
    (innerRef.infer bindings).shouldYields 4 (.TFn .TLit .TLit) ∧
      (AST.infer (.apply innerRef (.val (.lit bFalse))) bindings).shouldYields 5 .TLit
  | _ => false

#guard Malformed.WrongTypeIdFnOnItself.infer.shouldFail 3

#guard Malformed.WrongTypeIdFnOnFalse2.infer.shouldFail 4

#guard Malformed.applyLit2.infer.shouldFail 4

#guard Malformed.applyLit1.infer.shouldFail 2

end infer

end Trm

end Sanity
