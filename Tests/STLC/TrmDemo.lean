import «Tests».STLC.ValDemo

namespace Tests.STLC.Sanity
open Lp2lc.Active.Util
open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

variable [testEnv : TestEnv]

namespace Trm

def vFalse : Trm :=
  .val (.lit "false")

def vTrue : Trm :=
  .val (.lit "true")

def primitiveIdFn : Trm :=
  .val (.lam (λ _lift x => .ref (.inr x)) .primitive)

def primitiveIdFnOnFalse : Trm :=
  .apply primitiveIdFn vFalse

def get1st : Trm :=
  .val
    (.lam (λ _liftOuter x =>
      .val
        (.lam (λ liftInner _y => .ref (.inr (liftInner x))) .primitive))
      .primitive)

def get2nd : Trm :=
  .val
    (.lam (λ _liftOuter _x =>
      .val
        (.lam (λ _liftInner y => .ref (.inr y)) .primitive))
      .primitive)

def get1stOnTuple : Trm :=
  .apply
    (.apply get1st vFalse)
    vTrue

def get2ndOnTuple : Trm :=
  .apply
    (.apply get2nd vFalse)
    vTrue

def primitiveTrueFn : Trm :=
  .val
    (.lam (λ _lift _x =>
      .val (.lit "true"))
      .primitive)

def primitiveTrueFnOnFalse : Trm :=
  .apply primitiveTrueFn vFalse

namespace FreeCapture

def value : Val :=
  .lit "false"

/-- Runtime receipt for [value], minted through the fixture's executable bridge. -/
def receipt : refs.uid2val.UId :=
  testEnv.trm2valExeCtx.inv value

def directRef : Trm :=
  .ref (.inl receipt)

def capturedRef : Trm :=
  .val
    (.lam (λ _lift _x => .ref (.inl receipt)) .primitive)

def capturedRefOnFalse : Trm :=
  .apply capturedRef vFalse

end FreeCapture

namespace TypeHinted

def hintedFalse : Trm :=
  .val (.lit "false")

def hintedIdFn : Trm :=
  .val (.lam (λ _lift x => .ref (.inr x)) .primitive)

def hintedIdFnOnFalse : Trm :=
  .apply hintedIdFn hintedFalse

end TypeHinted

namespace Malformed

def applyIdFnOnItself : Trm :=
  .apply primitiveIdFn primitiveIdFn

def idFnOnFalse2 : Trm :=
  .apply applyIdFnOnItself vFalse

def primitiveApply : Trm :=
  .apply vFalse vTrue

def apply1 : Trm :=
  .apply
    (.apply primitiveIdFn vFalse)
    vTrue

def binderIdentityCounterexample
    (decEq : (B : UIdU) → DecidableEq B) : Trm :=
  .apply
    (.apply
      (.val
        (.lam
          (λ _liftOuter outer =>
            .val
              (.lam
                (λ {B} liftInner inner =>
                  let _ := decEq B
                  if inner = liftInner outer then
                    .ref (.inr inner)
                  else
                    .apply vFalse vTrue)
                .primitive))
          .primitive))
      vFalse)
    vTrue

end Malformed

end Trm

end Sanity
