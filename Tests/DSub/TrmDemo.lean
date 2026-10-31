import «Lp2lc».Active.DSub.Hash
import «Tests».DSub.ValDemo

namespace Tests.DSub.Sanity

open Lp2lc.Active.DSub Lp2lc.Active.Util
open Lean (toJson)

def bFalse := "false"

def bTrue := "true"

def vFalse : Val := .lit bFalse

def vTrue : Val := .lit bTrue

deriving instance BEq for Return

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
  .val (.fn (.TFn .TLit (.mk (λ _ => .TLit))) (.mk (λ fn => .ref fn .same)))

def higherOrderApplication : Trm :=
  .apply (.apply higherOrderId primitiveIdFn) vFalse

def primitiveLiteralIdFn : Trm :=
  .val (.fnPrimitive (.mk (λ _ => .TLit)) .lit)

def primitiveLiteralIdFnOnFalse : Trm :=
  .apply primitiveLiteralIdFn vFalse

def primitiveFirstFnOnTuple : Trm :=
  .apply
    (.apply (.val (.fnPrimitive (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit)))))
      (λ first => .fnPrimitive (.mk (λ _ => .TLit)) (λ _ => .lit first)))) vFalse) vTrue

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
  .apply (.val (.fnPrimitive (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit))))) .lit)) (.val (.lit bFalse))

def corruptedCallee : Trm :=
  .apply corruptApplication vTrue

def corruptedArgument : Trm :=
  .apply higherOrderId corruptApplication

def corruptedBody : Trm :=
  .apply (.val (.fn .TLit (.mk (λ _ => corruptApplication 1)))) vFalse

def illTypedPrimitiveResult : Trm :=
  .apply (.val (.fnPrimitive (.mk (λ _ => .TLit))
    (λ _ => .fn .TLit (.mk (λ _ => .apply (.val (.lit "bad")) (.val (.lit "bad"))))))) vFalse

def primitiveFnOnTuple : Trm :=
  .apply
    (.apply (.val (.fnPrimitive (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit)))))
      (λ _ => .fnPrimitive (.mk (λ _ => .TLit)) (λ _ => Val.idFn)))) vFalse) vTrue

end Corrupted

end Trm

end Tests.DSub.Sanity
