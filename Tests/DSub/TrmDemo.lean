import «Lp2lc».Active.DSub.Hash
import «Tests».DSub.ValDemo
import «Tests».DSub.TypDemo

namespace Tests.DSub.Sanity

open Lp2lc.Active.DSub Lp2lc.Active.Util
open Lean (toJson)

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

namespace InDSub

def boolType : Trm :=
  .val (.typeDef .TLit)

def fnType : Trm :=
  .val (.typeDef Typ.idFn)

def boundedId : Trm :=
  .val (.fn Typ.InDSub.boundedMember (.mk (λ value => .ref value .same)))

def boundedApplication : Trm :=
  .apply boundedId boolType

def selectedId : Trm :=
  .val (.fn Typ.InDSub.selectedBool (.mk (λ value => .ref value .same)))

def selectedApplication : Trm :=
  .apply selectedId vFalse

def selectedFnId : Trm :=
  .val (.fn Typ.InDSub.selectedFn (.mk (λ value => .ref value .same)))

def selectedFnApplication : Trm :=
  .apply (.apply selectedFnId primitiveIdFn) vTrue

namespace Malformed

def applyTypeDef : Trm :=
  .apply boolType vFalse

def wrongMember : Trm :=
  .apply boundedId (.val (.typeDef .TTop))

def wrongSelectedArgument : Trm :=
  .apply selectedId boolType

def wrongSelectedFnArgument : Trm :=
  .apply selectedFnId vFalse

end Malformed

namespace Undecidable

variable {n : Nat}

/-- Scala's `Negate[T]`, retaining the bound variable in the dependent result. -/
def Negate (bound : Typ n) : Typ n :=
  .TFn (.TMember .TBot bound) (.mk (λ x => .TSel (.ref x .same)))

def ExpandingBound : Typ n :=
  .TFn (.TMember .TBot .TTop) (.mk (λ x =>
    Negate (.TFn (.TMember .TBot (.TSel (.ref x .same))) (.mk (λ y =>
      Negate (.TSel (.ref y .same)))))))

/-- Elaborate a Scala result annotation `term: T` as `(λ result: T => result)(term)`.
This retains its subtype check using existing DSub syntax rather than dropping the annotation. -/
private def ascribed (term : Trm n) (typ : Typ n) : Trm n :=
  .apply (.val (.fn typ (.mk (λ result => .ref result .same)))) term

def narrowNegation1 : Trm :=
  .val (.fn (Negate .TTop) (.mk (λ value =>
    ascribed
      (.val (.fn (.TMember .TBot .TLit) (.mk (λ x =>
        .apply (.ref value (.lower .same)) (.ref x .same)))))
      (Negate .TLit))))

/-- Scala's method and function-valued versions have the same core AST. -/
abbrev narrowNegation2 : Trm := narrowNegation1

/-- The annotated method inside Scala's `narrowAccepted` compile-time probe. -/
def narrow : Trm :=
  .val (.fn (Negate .TTop) (.mk (λ value =>
    ascribed (.ref value .same) (Negate .TLit))))

/-- The annotated method inside Scala's `expandingSubtypingAccepted` probe. -/
def expandingSubtyping : Trm :=
  .val (.fn (.TMember .TBot ExpandingBound) (.mk (λ x0 =>
    .val (.fn (.TSel (.ref x0 .same)) (.mk (λ value =>
      ascribed (.ref value .same)
        (.TFn (.TMember .TBot (.TSel (.ref x0 (.lower .same)))) (.mk (λ x1 =>
          Negate (.TSel (.ref x1 .same)))))))))))

-- Scala's disabled cyclicBoundAccepted probe requires recursive objects, outside System DSub.

end Undecidable

end InDSub

end Trm

end Tests.DSub.Sanity
