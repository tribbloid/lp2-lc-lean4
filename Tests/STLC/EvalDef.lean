import «Tests».STLC.TrmDemo
import «Lp2lc».Active.STLC.Hash

namespace Tests.STLC.Sanity

open Lp2lc.Active.STLC Lp2lc.Active.Util

def falseValue : ExeVal := ⟨0, .lit bFalse, .empty⟩
def trueValue : ExeVal := ⟨0, .lit bTrue, .empty⟩
def freeBindings : ExeBindings := NatBindings.empty.set 0 trueValue
def capturedTrueValue : ExeVal := ⟨1, .lit bTrue, NatBindings.empty.set 1 falseValue⟩
def idFnValue : ExeVal := ⟨0, Val.idFn, .empty⟩
def get1stOnFalseValue : ExeVal :=
  ⟨1, .fn .TLit (.mk (λ _ => .ref
    (P' := { B := String, I := IndexEncoding.Serial, index := ⟨1⟩ }) .only (.lower .same))),
    NatBindings.empty.set 1 falseValue⟩
def outerValue : ExeVal := ⟨0, .lit "outer", .empty⟩
def capturedBindings : ExeBindings := NatBindings.empty.set 0 outerValue
def capturedClosure : ExeVal := ⟨0, Trm.FreeVarCapture.capturedValue, capturedBindings⟩
def callerBindings : ExeBindings := NatBindings.empty.set 0 capturedClosure
def shiftedBindings : ExeBindings := NatBindings.empty.set 1 outerValue

open Lean (Json toJson)

-- Compare runtime closures, including their contexts and captured bindings, in evaluator tests.
def closureSignature (closure : ExeVal) : Json :=
  match closure with
  | .mk n value captured =>
    let rec bindings (entries : ExeBindings) : Json :=
      match entries with
      | .empty => .null
      | .set rest index value => .arr #[bindings rest, toJson index, closureSignature value]
    .arr #[toJson n, astToJson value toJson toJson, bindings captured]
termination_by structural closure

instance : BEq (Return ExeVal) where -- TODO: violate the rule (double implementation): ExeEval BEq can already be inferred through BEq of AST
  beq first second :=
    match first, second with
    | .some first, .some second => closureSignature first == closureSignature second
    | .corrupted, .corrupted => true
    | _, _ => false

instance : Coe ExeVal (Return ExeVal) where
  coe value := .some value

namespace Trm

namespace FreeVarCapture

-- Share the captured primitive between evaluators, including its missing-capture failure.
def primitive : Val :=
  .fnPrimitive (.TFn .TLit .TLit) (λ _ => capturedValue)

def primitiveRefOnFalseTwice : Trm :=
  .apply (.apply directRef vFalse) vFalse

def directRefOnTrue : Trm :=
  .apply directRef vTrue

def shiftedRef : Trm 3 :=
  .ref (P' := { B := String, I := IndexEncoding.Serial, index := ⟨1⟩ }) .only (.lower (.lower .same))

end FreeVarCapture

def get1stOnFalse : Trm :=
  .apply get1st vFalse

def higherOrderId : Trm :=
  .val (.fn (.TFn .TLit .TLit) (.mk (λ fn => .ref fn .same)))

def higherOrderApplication : Trm :=
  .apply (.apply higherOrderId primitiveIdFn) vFalse

def primitiveLiteralIdFn : Trm :=
  .val (.fnPrimitive .TLit .lit)

def primitiveLiteralIdFnOnFalse : Trm :=
  .apply primitiveLiteralIdFn vFalse

def primitiveFirstFnOnTuple : Trm :=
  .apply
    (.apply (.val (.fnPrimitive (.TFn .TLit .TLit)
      (λ first => .fnPrimitive .TLit (λ _ => .lit first)))) vFalse) vTrue

namespace Corrupted

def corruptApplication (n : Nat := 0) : Trm n :=
  .apply (.val (.fnPrimitive (.TFn .TLit .TLit) .lit)) (.val (.lit bFalse))

def corruptedCallee : Trm :=
  .apply corruptApplication vTrue

def corruptedArgument : Trm :=
  .apply higherOrderId corruptApplication

def corruptedBody : Trm :=
  .apply (.val (.fn .TLit (.mk (λ _ => corruptApplication 1)))) vFalse

def illTypedPrimitiveResult : Trm :=
  .apply (.val (.fnPrimitive .TLit
    (λ _ => .fn .TLit (.mk (λ _ => .apply (.val (.lit "bad")) (.val (.lit "bad"))))))) vFalse

def missingPrimitiveCapture : Trm :=
  .apply (.val FreeVarCapture.primitive) vFalse

def primitiveFnOnTuple : Trm :=
  .apply
    (.apply (.val (.fnPrimitive (.TFn .TLit .TLit)
      (λ _ => .fnPrimitive .TLit (λ _ => Val.idFn)))) vFalse) vTrue

end Corrupted

namespace Malformed

def applyLitToApplication : Trm :=
  .apply vFalse primitiveIdFnOnFalse

def wrongNestedTIn : Trm :=
  .apply higherOrderId get1st

def primitiveLiteralIdFnOnFn : Trm :=
  .apply primitiveLiteralIdFn primitiveIdFn

end Malformed

end Trm

def capturedPrimitiveBindings : ExeBindings :=
  NatBindings.empty.set 0 ⟨0, Trm.FreeVarCapture.primitive, freeBindings⟩

end Tests.STLC.Sanity
