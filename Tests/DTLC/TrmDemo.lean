import Lean.Data.Json
import «Tests».DTLC.ValDemo

namespace Tests.DTLC.Sanity

open Lp2lc.Active.DTLC Lp2lc.Active.Util
open Lean (Json)

@[match_pattern] private abbrev bind := @Pre.Binder.mk

private def visit {P l} (self : Pre.AST P l) (get : ∀ index, P.I.getTRef index)
    (sig : P.I.Index ⊕ P.B → Json) : Json :=
  match self with
  | .TLit => "primitive"
  | .TFn tIn (bind output) =>
    .arr #["fn", visit tIn get sig, visit (output (get P.Next.index)) get sig]
  | .lit repr => .arr #["lit", sig (.inr repr)]
  | .fn tIn (bind body) =>
    .arr #["lam", visit (body (get P.Next.index)) get sig, visit tIn get sig]
  | .fnPrimitive (bind output) _ => .arr #["primitiveFn", visit (output (get P.Next.index)) get sig]
  | .val v => .arr #["val", visit v get sig]
  | .apply fnTerm arg =>
    .arr #["apply", visit fnTerm get sig, visit arg get sig]
  | .ref _ under => .arr #["ref", sig (.inl under.sourceIndex)]

def astToJson {n l} (self : AST n l)
    (sigC : Nat → Json) (sigB : String → Json) : Json :=
  visit self (λ _ => .only) (Sum.elim (sigC ∘ ULift.down) sigB)

def astBEq {n m l} (a : AST n l) (b : AST m l)
    (sigC : Nat → Json) (sigB : String → Json) (otherSigC : Nat → Json := sigC) : Bool :=
  astToJson a sigC sigB == astToJson b otherSigC sigB
-- TODO: delete above, AST already have BEq instance

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

end Tests.DTLC.Sanity
