import «Lp2lc».Active.STLC.Serial.__Infer
import «Tests».STLC.TrmDemo

namespace Tests.STLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.STLC

section infer

local instance : BEq Typ := ⟨λ first second => decide (first ≤ second)⟩

private def literalValue : ExeValue := .mk 0 (.lit bTrue) .empty

private def fnValue : ExeValue :=
  .mk 0 (.fn .TLit (.mk (λ proxy => .ref proxy .same))) .empty

private def literalBindings : ExeBindings := Bindings.empty.set 0 literalValue

private def fnBindings : ExeBindings := (Bindings.empty.set 0 fnValue).set 1 fnValue

private def mixedBindings : ExeBindings := fnBindings.set 1 literalValue

private def innerRef : Trm 1 := .ref (P' := { B := String, I := .Serial, index := 1 }) .only .same

#guard vFalse.infer.shouldYieldsBool 1 .TLit

#guard vTrue.infer.shouldYieldsBool 1 .TLit

#guard primitiveIdFn.infer.shouldYieldsBool 2 (.TFn .TLit .TLit)

#guard (AST.infer (.val (.fn (.TFn .TLit (.TFn .TLit .TLit))
  (.mk (λ proxy => .ref proxy .same))) : Trm 7)).shouldYieldsBool 2
  (.TFn (.TFn .TLit (.TFn .TLit .TLit)) (.TFn .TLit (.TFn .TLit .TLit)))

#guard primitiveIdFnOnFalse.infer.shouldYieldsBool 3 .TLit

#guard get1st.infer.shouldYieldsBool 3 (.TFn .TLit (.TFn .TLit .TLit))

#guard get2nd.infer.shouldYieldsBool 3 (.TFn .TLit (.TFn .TLit .TLit))

#guard get1stOnTuple.infer.shouldYieldsBool 5 .TLit

#guard get2ndOnTuple.infer.shouldYieldsBool 5 .TLit

#guard primitiveTrueFn.infer.shouldYieldsBool 2 (.TFn .TLit .TLit)

#guard primitiveTrueFnOnFalse.infer.shouldYieldsBool 3 .TLit

#guard TypeHinted.hintedFalse.infer.shouldYieldsBool 1 .TLit

#guard TypeHinted.hintedIdFn.infer.shouldYieldsBool 2 (.TFn .TLit .TLit)

#guard TypeHinted.hintedIdFnOnFalse.infer.shouldYieldsBool 3 .TLit

#guard (FreeCapture.directRef.infer literalBindings).shouldYieldsBool 2 .TLit

#guard (AST.infer (.ref FreeCapture.freeSlot .same : Trm 0) literalBindings).shouldYieldsBool 2 .TLit

#guard (FreeCapture.directRef.infer fnBindings).shouldYieldsBool 3 (.TFn .TLit .TLit)

#guard (FreeCapture.capturedRef.infer fnBindings).shouldYieldsBool 4
  (.TFn .TLit (.TFn .TLit .TLit))

#guard (FreeCapture.capturedRefOnFalse.infer fnBindings).shouldYieldsBool 5 (.TFn .TLit .TLit)

#guard (primitiveIdFn.infer fnBindings).shouldYieldsBool 2 (.TFn .TLit .TLit)

#guard (primitiveIdFn.infer mixedBindings).shouldYieldsBool 2 (.TFn .TLit .TLit)

#guard (FreeCapture.directRef.infer mixedBindings).shouldYieldsBool 3 (.TFn .TLit .TLit)

#guard (innerRef.infer mixedBindings).shouldYieldsBool 2 .TLit

#guard (AST.infer (.apply FreeCapture.directRef primitiveIdFn) fnBindings).shouldFailBool 4

#guard match FreeCapture.capturedRef.eval (Bindings.empty.set 0 literalValue) 1 with
  | .yield (some closure) =>
    let bindings := mixedBindings.set 1 closure
    (innerRef.infer bindings).shouldYieldsBool 4 (.TFn .TLit .TLit) &&
      (AST.infer (.apply innerRef (.val (.lit bFalse))) bindings).shouldYieldsBool 5 .TLit
  | _ => false

#guard Malformed.applyIdFnOnItself.infer.shouldFailBool 3

#guard Malformed.idFnOnFalse2.infer.shouldFailBool 4

#guard Malformed.apply1.infer.shouldFailBool 4

#guard Malformed.primitiveApply.infer.shouldFailBool 2

end infer

end Trm

end Sanity
