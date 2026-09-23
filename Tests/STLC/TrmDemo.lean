import «Tests».STLC.ValDemo

namespace Tests.STLC.Sanity
open Lp2lc.Active.Util
open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

variable [testEnv : TestEnv]

/-- The case files' demo data: the String literals coerce into the fixture's bytecode
carrier through the fixture's own [TestEnv.bEq] coercion instance. -/
def bFalse : refs.Parameters.B := "false"

def bTrue : refs.Parameters.B := "true"

namespace Trm

def vFalse : Trm :=
  .val (.lit bFalse)

def vTrue : Trm :=
  .val (.lit bTrue)

def primitiveIdFn : Trm :=
  .val (.fn (.mk (.ref (.inr ()))) .TLit)

def primitiveIdFnOnFalse : Trm :=
  .apply primitiveIdFn vFalse

def get1st : Trm :=
  .val
    (.fn
      (.mk
        (.val
          (.fn (.mk (.ref (.inl (.inr ())))) .TLit)))
      .TLit)

def get2nd : Trm :=
  .val
    (.fn
      (.mk
        (.val
          (.fn (.mk (.ref (.inr ()))) .TLit)))
      .TLit)

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
    (.fn (.mk (.val (.lit bTrue))) .TLit)

def primitiveTrueFnOnFalse : Trm :=
  .apply primitiveTrueFn vFalse

namespace FreeCapture

def value : Val :=
  .lit bFalse

/-- Runtime receipt for [value], minted through the fixture's executable bridge. -/
def receipt : I.C :=
  testEnv.trm2valExeCtx.inv value

def directRef : Trm :=
  .ref receipt

def capturedRef : Trm :=
  .val
    (.fn (.mk (.ref (.inl receipt))) .TLit)

def capturedRefOnFalse : Trm :=
  .apply capturedRef vFalse

end FreeCapture

namespace TypeHinted

def hintedFalse : Trm :=
  .val (.lit bFalse)

def hintedIdFn : Trm :=
  .val (.fn (.mk (.ref (.inr ()))) .TLit)

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
