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
  .val (.lam (λ x => .ref x) .primitive)

def primitiveIdFnOnFalse : Trm :=
  .apply primitiveIdFn vFalse

def get1st : Trm :=
  .val
    (.lam (λ x =>
      .val
        (.lam (λ _y => .ref x) .primitive))
      .primitive)

def get2nd : Trm :=
  .val
    (.lam (λ _x =>
      .val
        (.lam (λ y => .ref y) .primitive))
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

namespace TypeHinted

def hintedFalse : Trm :=
  .val (.lit "false")

def hintedIdFn : Trm :=
  .val (.lam (λ x => .ref x) .primitive)

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

def binderIdentityCounterexample : Trm :=
  let input : Val := .lit "false"
  let receipt := testEnv.trm2valCtx.inv input
  .apply
    (.val
      (.lam (λ {C} [embedding : Greater C refs.uid2val.UId] (arg : C) =>
        let _ : DecidableEq C := testEnv.decidableEq C
        if arg = embedding.coe receipt then
          .apply (.val (.lit "false")) (.val (.lit "true"))
        else
          .ref arg)
        .primitive))
    (.val input)

end Malformed

end Trm

end Sanity
