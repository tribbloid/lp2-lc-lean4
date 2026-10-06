import «Lp2lc».Active.STLC.Serial.__Infer
import «Tests».STLC.TrmDemo

namespace Tests.STLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.STLC

section infer

local instance : BEq Typ := ⟨λ first second => decide (first ≤ second)⟩

private def literalValue : ExeValue := .mk 0 (.lit bTrue) (λ _ => none)

private def literalBindings : AST.BuildBindings := λ _ => some (.inl literalValue)

private def typeBindings : AST.BuildBindings := λ _ => some (.inr (.TFn .TLit .TLit))

private def mixedBindings : AST.BuildBindings := λ index =>
  match index with
  | 0 => typeBindings index
  | 1 => literalBindings index
  | _ => none

private def innerRef : Trm 1 := .ref (P' := { B := String, I := .Serial, index := 1 }) .only .same

#guard vFalse.infer.shouldYieldsBool 1 .TLit

#guard vTrue.infer.shouldYieldsBool 1 .TLit

#guard primitiveIdFn.infer.shouldYieldsBool 2 (.TFn .TLit .TLit)

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

#guard (FreeCapture.directRef.inferInternal literalBindings).shouldYieldsBool 2 .TLit

#guard (AST.inferInternal (.ref FreeCapture.freeSlot .same : Trm 0) literalBindings).shouldYieldsBool 2 .TLit

#guard (FreeCapture.directRef.inferInternal typeBindings).shouldYieldsBool 1 (.TFn .TLit .TLit)

#guard (FreeCapture.capturedRef.inferInternal typeBindings).shouldYieldsBool 2
  (.TFn .TLit (.TFn .TLit .TLit))

#guard (FreeCapture.capturedRefOnFalse.inferInternal typeBindings).shouldYieldsBool 3 (.TFn .TLit .TLit)

#guard (primitiveIdFn.inferInternal typeBindings).shouldYieldsBool 2 (.TFn .TLit .TLit)

#guard (primitiveIdFn.inferInternal mixedBindings).shouldYieldsBool 2 (.TFn .TLit .TLit)

#guard (FreeCapture.directRef.inferInternal mixedBindings).shouldYieldsBool 1 (.TFn .TLit .TLit)

#guard (innerRef.inferInternal mixedBindings).shouldYieldsBool 2 .TLit

#guard (AST.inferInternal (.apply FreeCapture.directRef primitiveIdFn) typeBindings).shouldFailBool 3

#guard match FreeCapture.capturedRef.eval (λ _ => some literalValue) 1 with
  | .yield (some closure) =>
    let bindings := λ index => if index = 1 then some (.inl closure) else mixedBindings index
    (innerRef.inferInternal bindings).shouldYieldsBool 4 (.TFn .TLit .TLit) &&
      (AST.inferInternal (.apply innerRef (.val (.lit bFalse))) bindings).shouldYieldsBool 5 .TLit
  | _ => false

#guard Malformed.applyIdFnOnItself.infer.shouldFailBool 3

#guard Malformed.idFnOnFalse2.infer.shouldFailBool 4

#guard Malformed.apply1.infer.shouldFailBool 4

#guard Malformed.primitiveApply.infer.shouldFailBool 2

end infer

end Trm

end Sanity
