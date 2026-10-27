import «Tests».STLC.ValDemo

namespace Tests.STLC.Sanity

open Lp2lc.Active.STLC
open Lp2lc.Active.Util

def bFalse := "false"

def bTrue := "true"

namespace Trm

def vFalse : Trm :=
  .val (.lit bFalse)

def vTrue : Trm :=
  .val (.lit bTrue)

def primitiveIdFn : Trm :=
  .val (.fn .TLit (.mk (λ proxy => .ref proxy .same)))

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

namespace FreeVarCapture

/-- A symbolic outer-context slot used by the syntax-only capture examples. -/
def freeSlot : IndexEncoding.SerialProxy 0 := .only

def directRef : Trm 0 :=
  .ref freeSlot .same

def capturedValue : Val :=
  .fn .TLit (.mk (λ _ => .ref freeSlot (.lower .same)))

def capturedRef : Trm :=
  .val capturedValue

def capturedRefOnFalse : Trm :=
  .apply capturedRef (.val (.lit bFalse))

end FreeVarCapture

namespace TypeHinted
-- TODO: this namespace should be deleted, current STLC syntax has no type hint, many fixtures in it are just duplicates

def hintedFalse : Trm :=
  .val (.lit bFalse)

def hintedIdFn : Trm :=
  .val (.fn .TLit (.mk (λ proxy => .ref proxy .same)))

def hintedIdFnOnFalse : Trm :=
  .apply hintedIdFn hintedFalse

end TypeHinted

namespace Malformed

def WrongTIn : Trm :=
  .apply primitiveIdFn primitiveIdFn

def ContainWrongTIn : Trm :=
  .apply WrongTIn vFalse

def applyLit1 : Trm :=
  .apply vFalse vTrue

def applyLit2 : Trm :=
  .apply (.apply primitiveIdFn vFalse) vTrue

end Malformed

end Trm

end Tests.STLC.Sanity
