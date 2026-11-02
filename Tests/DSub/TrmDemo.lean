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
  .pure (.val Val.idFn)

def primitiveIdFnOnFalse : Trm :=
  .apply primitiveIdFn vFalse

def get1st : Trm :=
  .pure (.val (.fn .TLit
      (.mk (λ first =>
        .pure (.val (.fn .TLit (.mk (λ _ => .pure (.ref first (.lower .same))))))))))

def get2nd : Trm :=
  .pure (.val (.fn .TLit
      (.mk (λ _ =>
        .pure (.val (.fn .TLit (.mk (λ second => .pure (.ref second .same)))))))))

def get1stOnTuple : Trm :=
  .apply (.apply get1st vFalse) vTrue

def get2ndOnTuple : Trm :=
  .apply (.apply get2nd vFalse) vTrue

def primitiveTrueFn : Trm :=
  .pure (.val (.fn .TLit (.mk (λ _ => .pure (.val (.lit bTrue))))))

def primitiveTrueFnOnFalse : Trm :=
  .apply primitiveTrueFn vFalse

def get1stOnFalse : Trm :=
  .apply get1st vFalse

def higherOrderId : Trm :=
  .pure (.val (.fn (.TFn .TLit (.mk (λ _ => .TLit))) (.mk (λ fn => .pure (.ref fn .same)))))

def higherOrderApplication : Trm :=
  .apply (.apply higherOrderId primitiveIdFn) vFalse

def primitiveLiteralIdFn : Trm :=
  .pure (.val (.fnPrimitive (.mk (λ _ => .TLit)) .lit))

def primitiveLiteralIdFnOnFalse : Trm :=
  .apply primitiveLiteralIdFn vFalse

def primitiveFirstFnOnTuple : Trm :=
  .apply
    (.apply (.pure (.val (.fnPrimitive (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit)))))
      (λ first => .fnPrimitive (.mk (λ _ => .TLit)) (λ _ => .lit first))))) vFalse) vTrue

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
  .apply (.pure (.val (.fnPrimitive (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit))))) .lit))) (.pure (.val (.lit bFalse)))

def corruptedCallee : Trm :=
  .apply corruptApplication vTrue

def corruptedArgument : Trm :=
  .apply higherOrderId corruptApplication

def corruptedBody : Trm :=
  .apply (.pure (.val (.fn .TLit (.mk (λ _ => corruptApplication 1))))) vFalse

def illTypedPrimitiveResult : Trm :=
  .apply (.pure (.val (.fnPrimitive (.mk (λ _ => .TLit))
    (λ _ => .fn .TLit (.mk (λ _ => .apply (.pure (.val (.lit "bad"))) (.pure (.val (.lit "bad"))))))))) vFalse

def primitiveFnOnTuple : Trm :=
  .apply
    (.apply (.pure (.val (.fnPrimitive (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit)))))
      (λ _ => .fnPrimitive (.mk (λ _ => .TLit)) (λ _ => Val.idFn))))) vFalse) vTrue

end Corrupted

namespace InDSub

variable {n : Nat}

/-- Elaborate a Scala result annotation `term: T` as `(λ result: T => result)(term)`.
This retains the required subtype check without adding a production ascription form. -/
private def ascribed (term : Trm n) (typ : Typ n) : Trm n :=
  .apply (.pure (.val (.fn typ (.mk (λ result => .pure (.ref result .same)))))) term

def boolType : Trm :=
  .pure (.val (.typeDef .TLit))

def fnType : Trm :=
  .pure (.val (.typeDef Typ.idFn))

def boundedId : Trm :=
  .pure (.val (.fn Typ.InDSub.boundedMember (.mk (λ value => .pure (.ref value .same)))))

def boundedApplication : Trm :=
  .apply boundedId boolType

def selectedId : Trm :=
  .pure (.val (.fn Typ.InDSub.selectedBool (.mk (λ value => .pure (.ref value .same)))))

def selectedApplication : Trm :=
  .apply selectedId vFalse

def selectedFnId : Trm :=
  .pure (.val (.fn Typ.InDSub.selectedFn (.mk (λ value => .pure (.ref value .same)))))

def selectedFnApplication : Trm :=
  .apply (.apply selectedFnId primitiveIdFn) vTrue

def dependentId : Trm :=
  .pure (.val (.fn Typ.InDSub.abstractMember (.mk (λ x =>
    .pure (.val (.fn (.TSel (.ref x .same)) (.mk (λ value => .pure (.ref value .same)))))))))

def dependentApplication : Trm :=
  .apply (.apply dependentId boolType) vFalse

def dependentType : Trm :=
  .pure (.val (.fn Typ.InDSub.abstractMember (.mk (λ x =>
    .pure (.val (.typeDef (.TSel (.ref x .same))))))))

def dependentTypeApplication : Trm :=
  .apply dependentType boolType

def dependentFnTypeApplication : Trm :=
  .apply dependentType fnType

def capturedId : Trm :=
  .pure (.val (.fn Typ.InDSub.abstractMember (.mk (λ x =>
    .pure (.val (.fn Typ.InDSub.abstractMember (.mk (λ _ =>
      .pure (.val (.fn (.TSel (.ref x (.lower .same))) (.mk (λ value =>
        .pure (.ref value .same)))))))))))))

def capturedApplication : Trm :=
  .apply (.apply (.apply capturedId boolType) fnType) vFalse

def capturedFnApplication : Trm :=
  .apply (.apply (.apply capturedId fnType) boolType) primitiveIdFn

def boundedDependentId : Trm :=
  .pure (.val (.fn Typ.InDSub.boundedMember (.mk (λ x =>
    .pure (.val (.fn (.TSel (.ref x .same)) (.mk (λ value =>
      ascribed (.pure (.ref value .same)) .TLit))))))))

def boundedDependentApplication : Trm :=
  .apply (.apply boundedDependentId boolType) vTrue

namespace Malformed

def applyTypeDef : Trm :=
  .apply boolType vFalse

def wrongMember : Trm :=
  .apply boundedId (.pure (.val (.typeDef .TTop)))

def wrongSelectedArgument : Trm :=
  .apply selectedId boolType

def wrongSelectedFnArgument : Trm :=
  .apply selectedFnId vFalse

def wrongDependentArgument : Trm :=
  .apply (.apply dependentId boolType) boolType

end Malformed

namespace Undecidable

/-- Scala's `Negate[T]`, with its lexical variable represented as a pure reference. -/
def Negate (bound : Typ n) : Typ n :=
  .TFn (.TMember .TBot bound) (.mk (λ x => .TSel (.ref x .same)))

def ExpandingBound : Typ n :=
  .TFn (.TMember .TBot .TTop) (.mk (λ x =>
    Negate (.TFn (.TMember .TBot (.TSel (.ref x .same))) (.mk (λ y =>
      Negate (.TSel (.ref y .same)))))))

def narrowNegation1 : Trm :=
  .pure (.val (.fn (Negate .TTop) (.mk (λ value =>
    ascribed
      (.pure (.val (.fn (.TMember .TBot .TLit) (.mk (λ x =>
        .apply (.pure (.ref value (.lower .same))) (.pure (.ref x .same)))))))
      (Negate .TLit)))))

/-- Scala's method and function-valued versions have the same core AST. -/
abbrev narrowNegation2 : Trm := narrowNegation1

/-- The annotated method inside Scala's `narrowAccepted` compile-time probe. -/
def narrow : Trm :=
  .pure (.val (.fn (Negate .TTop) (.mk (λ value =>
    ascribed (.pure (.ref value .same)) (Negate .TLit)))))

/-- The annotated method inside Scala's `expandingSubtypingAccepted` probe. -/
def expandingSubtyping : Trm :=
  .pure (.val (.fn (.TMember .TBot ExpandingBound) (.mk (λ x0 =>
    .pure (.val (.fn (.TSel (.ref x0 .same)) (.mk (λ value =>
      ascribed (.pure (.ref value .same))
        (.TFn (.TMember .TBot (.TSel (.ref x0 (.lower .same)))) (.mk (λ x1 =>
          Negate (.TSel (.ref x1 .same)))))))))))))

-- Scala's disabled cyclicBoundAccepted probe requires recursive objects, outside System DSub.

end Undecidable

end InDSub

end Trm

end Tests.DSub.Sanity
