import «Tests».STLC.ValDemo
import «Lp2lc».Active.STLC.Hash

namespace Tests.STLC.Sanity

open Lp2lc.Active.STLC Lp2lc.Active.Util
open Lean (toJson)

def bFalse := "false"

def bTrue := "true"

def vFalse : Val := .lit bFalse

def vTrue : Val := .lit bTrue

deriving instance BEq for Return

-- Compare returned syntax using binder offsets, without requiring expected runtime environments.
abbrev shouldYieldSyntax (computation : RecOpt (Return ExeVal)) (fuel : Nat) (expected : Return Val) : Prop :=
  let offset (n index : Nat) := toJson (Int.ofNat index - Int.ofNat n)
  letI : BEq ExeVal := ⟨λ actual expected =>
    astBEq actual.value expected.value (offset actual.n) toJson (offset expected.n)⟩
  computation.shouldYield fuel (expected.map (λ value => ⟨0, value, .empty⟩))

namespace Trm

def primitiveIdFn : Trm :=
  .val Val.idFn

def primitiveIdFnOnFalse : Trm :=
  .apply primitiveIdFn vFalse

def get1st : Trm :=
  .val
    (.fn .TLit
      (.mk (λ first =>
        .val (.fn .TLit (.mk (λ _ => .ref first (.lower .same)))))))

def get2nd : Trm :=
  .val
    (.fn .TLit
      (.mk (λ _ =>
        .val (.fn .TLit (.mk (λ second => .ref second .same))))))

def get1stOnTuple : Trm :=
  .apply (.apply get1st vFalse) vTrue

def get2ndOnTuple : Trm :=
  .apply (.apply get2nd vFalse) vTrue

def primitiveTrueFn : Trm :=
  .val (.fn .TLit (.mk (λ _ => .val (.lit bTrue))))

def primitiveTrueFnOnFalse : Trm :=
  .apply primitiveTrueFn vFalse

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

-- Free-variable capture fixtures remain disabled while their test setup is simplified.
-- namespace FreeVarCapture

-- /-- A symbolic outer-context slot used by the syntax-only capture examples. -/
-- def freeSlot : IndexEncoding.SerialProxy 0 := .only

-- def directRef : Trm 0 :=
--   .ref freeSlot .same

-- def capturedValue : Val :=
--   .fn .TLit (.mk (λ _ => .ref freeSlot (.lower .same)))

-- def capturedRef : Trm :=
--   .val capturedValue

-- def capturedRefOnFalse : Trm :=
--   .apply capturedRef vFalse

-- -- Share the captured primitive between evaluators, including its missing-capture failure.
-- def primitive : Val :=
--   .fnPrimitive (.TFn .TLit .TLit) (λ _ => capturedValue)

-- def primitiveRefOnFalseTwice : Trm :=
--   .apply (.apply directRef vFalse) vFalse

-- def directRefOnTrue : Trm :=
--   .apply directRef vTrue

-- def shiftedRef : Trm 3 :=
--   .ref (P' := { B := String, I := IndexEncoding.Serial, index := ⟨1⟩ }) .only (.lower (.lower .same))

-- def capturedPrimitiveBindings : ExeBindings :=
--   NatBindings.empty.set 0 ⟨0, primitive, freeBindings⟩

-- end FreeVarCapture

namespace Malformed

def WrongTIn : Trm :=
  .apply primitiveIdFn primitiveIdFn

def ContainWrongTIn : Trm :=
  .apply WrongTIn vFalse

def applyLit1 : Trm :=
  .apply vFalse vTrue

def applyLit2 : Trm :=
  .apply (.apply primitiveIdFn vFalse) vTrue

def applyLitToApplication : Trm :=
  .apply vFalse primitiveIdFnOnFalse

def wrongNestedTIn : Trm :=
  .apply higherOrderId get1st

def primitiveLiteralIdFnOnFn : Trm :=
  .apply primitiveLiteralIdFn primitiveIdFn

end Malformed

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

-- The declared curried type is valid; the callback violates its final literal result type at runtime.
def primitiveFnOnTuple : Trm :=
  .apply
    (.apply (.val (.fnPrimitive (.TFn .TLit .TLit)
      (λ _ => .fnPrimitive .TLit (λ _ => Val.idFn)))) vFalse) vTrue

end Corrupted

end Trm

end Tests.STLC.Sanity
