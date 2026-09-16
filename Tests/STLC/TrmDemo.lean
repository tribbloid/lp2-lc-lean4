import «Tests».STLC.ValDemo

namespace Tests.STLC.Sanity
open Lp2lc.Active.Util
open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

variable [testEnv : TestEnv] [testEnvString : TestEnv.StringData testEnv]

/-- The case files' demo data: the String literals cast into the fixture's data
carrier through the case files' [TestEnv.StringData] assumption. -/
def dFalse : refs.Parameters.D := ofRepr "false"

def dTrue : refs.Parameters.D := ofRepr "true"

namespace Trm

def vFalse : Trm :=
  .val (.lit dFalse)

def vTrue : Trm :=
  .val (.lit dTrue)

def primitiveIdFn : Trm :=
  .val (.lam (.mk (.ref (.inr ()))) .primitive)

def primitiveIdFnOnFalse : Trm :=
  .apply primitiveIdFn vFalse

def get1st : Trm :=
  .val
    (.lam
      (.mk
        (.val
          (.lam (.mk (.ref (.inl (.inr ())))) .primitive)))
      .primitive)

def get2nd : Trm :=
  .val
    (.lam
      (.mk
        (.val
          (.lam (.mk (.ref (.inr ()))) .primitive)))
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
    (.lam
      (.mk (.val (.lit dTrue)))
      .primitive)

def primitiveTrueFnOnFalse : Trm :=
  .apply primitiveTrueFn vFalse

namespace FreeCapture

def value : Val :=
  .lit dFalse

/-- Runtime receipt for [value], minted through the fixture's executable bridge. -/
def receipt : I.C :=
  testEnv.trm2valExeCtx.inv value

def directRef : Trm :=
  .ref receipt

def capturedRef : Trm :=
  .val
    (.lam (.mk (.ref (.inl receipt))) .primitive)

def capturedRefOnFalse : Trm :=
  .apply capturedRef vFalse

end FreeCapture

namespace TypeHinted

def hintedFalse : Trm :=
  .val (.lit dFalse)

def hintedIdFn : Trm :=
  .val (.lam (.mk (.ref (.inr ()))) .primitive)

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

end Malformed

end Trm

end Sanity
