import «Lp2lc».Active.STLC.Serial.__Infer
import «Tests».STLC.TrmDemo

namespace Tests.STLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.STLC

section infer

local instance : BEq Typ := ⟨λ first second => decide (first ≤ second)⟩

private def literalValue : ExeValue := .mk 0 (.lit bTrue) (λ _ => none)

private def fnValue : ExeValue :=
  .mk 0 (.fn .TLit (.mk (λ proxy => .ref proxy .same))) (λ _ => none)

private def literalBindings : ExeBindings := λ _ => some literalValue

private def fnBindings : ExeBindings := λ _ => some fnValue

private def mixedBindings : ExeBindings := λ index =>
  match index with
  | 0 => fnBindings index
  | 1 => literalBindings index
  | _ => none

private def innerRef : Trm 1 := .ref (P' := { B := String, I := .Serial, index := 1 }) .only .same

#guard (AST.infer vFalse).shouldYieldsBool 1 .TLit

#guard (AST.infer vTrue).shouldYieldsBool 1 .TLit

#guard (AST.infer primitiveIdFn).shouldYieldsBool 2 (.TFn .TLit .TLit)

#guard (AST.infer (.val (.fn (.TFn .TLit (.TFn .TLit .TLit))
  (.mk (λ proxy => .ref proxy .same))) : Trm 7)).shouldYieldsBool 2
  (.TFn (.TFn .TLit (.TFn .TLit .TLit)) (.TFn .TLit (.TFn .TLit .TLit)))

#guard (AST.infer primitiveIdFnOnFalse).shouldYieldsBool 3 .TLit

#guard (AST.infer get1st).shouldYieldsBool 3 (.TFn .TLit (.TFn .TLit .TLit))

#guard (AST.infer get2nd).shouldYieldsBool 3 (.TFn .TLit (.TFn .TLit .TLit))

#guard (AST.infer get1stOnTuple).shouldYieldsBool 5 .TLit

#guard (AST.infer get2ndOnTuple).shouldYieldsBool 5 .TLit

#guard (AST.infer primitiveTrueFn).shouldYieldsBool 2 (.TFn .TLit .TLit)

#guard (AST.infer primitiveTrueFnOnFalse).shouldYieldsBool 3 .TLit

#guard (AST.infer TypeHinted.hintedFalse).shouldYieldsBool 1 .TLit

#guard (AST.infer TypeHinted.hintedIdFn).shouldYieldsBool 2 (.TFn .TLit .TLit)

#guard (AST.infer TypeHinted.hintedIdFnOnFalse).shouldYieldsBool 3 .TLit

#guard (AST.infer FreeCapture.directRef literalBindings).shouldYieldsBool 2 .TLit

#guard (AST.infer (.ref FreeCapture.freeSlot .same : Trm 0) literalBindings).shouldYieldsBool 2 .TLit

#guard (AST.infer FreeCapture.directRef fnBindings).shouldYieldsBool 3 (.TFn .TLit .TLit)

#guard (AST.infer FreeCapture.capturedRef fnBindings).shouldYieldsBool 4
  (.TFn .TLit (.TFn .TLit .TLit))

#guard (AST.infer FreeCapture.capturedRefOnFalse fnBindings).shouldYieldsBool 5 (.TFn .TLit .TLit)

#guard (AST.infer primitiveIdFn fnBindings).shouldYieldsBool 2 (.TFn .TLit .TLit)

#guard (AST.infer primitiveIdFn mixedBindings).shouldYieldsBool 2 (.TFn .TLit .TLit)

#guard (AST.infer FreeCapture.directRef mixedBindings).shouldYieldsBool 3 (.TFn .TLit .TLit)

#guard (innerRef.infer mixedBindings).shouldYieldsBool 2 .TLit

#guard (AST.infer (.apply FreeCapture.directRef primitiveIdFn) fnBindings).shouldFailBool 4

#guard match AST.eval FreeCapture.capturedRef (λ _ => some literalValue) 1 with
  | .yield (some closure) =>
    let bindings := λ index => if index = 1 then some closure else mixedBindings index
    (innerRef.infer bindings).shouldYieldsBool 4 (.TFn .TLit .TLit) &&
      (AST.infer (.apply innerRef (.val (.lit bFalse))) bindings).shouldYieldsBool 5 .TLit
  | _ => false

#guard (AST.infer Malformed.applyIdFnOnItself).shouldFailBool 3

#guard (AST.infer Malformed.idFnOnFalse2).shouldFailBool 4

#guard (AST.infer Malformed.apply1).shouldFailBool 4

#guard (AST.infer Malformed.primitiveApply).shouldFailBool 2

end infer

end Trm

end Sanity
