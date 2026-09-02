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
  .val (.lam (λ x => .ref x.val) .primitive)

def primitiveIdFnOnFalse : Trm :=
  .apply primitiveIdFn vFalse

def get1st : Trm :=
  .val
    (.lam (λ x =>
      .val
        (.lam (λ _y => .ref x.val) .primitive))
      .primitive)

def get2nd : Trm :=
  .val
    (.lam (λ _x =>
      .val
        (.lam (λ y => .ref y.val) .primitive))
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
    (.lam (λ _x =>
      .val (.lit "true"))
      .primitive)

def primitiveTrueFnOnFalse : Trm :=
  .apply primitiveTrueFn vFalse

namespace FreeCapture

def value : Val :=
  .lit "false"

/-- Runtime receipt for [value], minted through the fixture's executable bridge. -/
def receipt : refs.Parameters.C :=
  (testEnv.trm2valExeCtx.inv value).val

def directRef : Trm :=
  .ref receipt

def capturedRef : Trm :=
  .val
    (.lam (λ _x => .ref receipt) .primitive)

def capturedRefOnFalse : Trm :=
  .apply capturedRef vFalse

end FreeCapture

namespace TypeHinted

def hintedFalse : Trm :=
  .val (.lit "false")

def hintedIdFn : Trm :=
  .val (.lam (λ x => .ref x.val) .primitive)

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
    (decEq : (C : UIdU) → DecidableEq C) : Trm :=
  .apply
    (.apply
      (.val
        (.lam
          (λ outer =>
            .val
              (.lam
                (λ inner =>
                  let _ := decEq refs.Parameters.C
                  if inner.val = outer.val then
                    .ref inner.val
                  else
                    .apply vFalse vTrue)
                .primitive))
          .primitive))
      vFalse)
    vTrue

end Malformed

end Trm

end Sanity
