import «Tests».STLC.ValDemo

namespace Tests.STLC.Sanity

open Lp2lc.Active.STLC
open Lp2lc.Active.Util

def bFalse := "false"

def bTrue := "true"

namespace Trm

def vFalse : AST 0 .trm :=
  .val (.lit bFalse)

def vTrue : AST 0 .trm :=
  .val (.lit bTrue)

def primitiveIdFn : AST 0 .trm :=
  .val (.fn .TLit (.mk (λ proxy => .ref proxy .same)))

def primitiveIdFnOnFalse : AST 0 .trm :=
  .apply primitiveIdFn vFalse

def get1st : AST 0 .trm :=
  .val
    (.fn .TLit
      (.mk (λ first =>
        .val (.fn .TLit (.mk (λ _ => .ref first (.lower .same)))))))

def get2nd : AST 0 .trm :=
  .val
    (.fn .TLit
      (.mk (λ _ =>
        .val (.fn .TLit (.mk (λ second => .ref second .same))))))

def get1stOnTuple : AST 0 .trm :=
  .apply (.apply get1st vFalse) vTrue

def get2ndOnTuple : AST 0 .trm :=
  .apply (.apply get2nd vFalse) vTrue

def primitiveTrueFn : AST 0 .trm :=
  .val (.fn .TLit (.mk (λ _ => .val (.lit bTrue))))

def primitiveTrueFnOnFalse : AST 0 .trm :=
  .apply primitiveTrueFn vFalse

namespace FreeCapture

/-- A symbolic outer-context slot used by the syntax-only capture examples. -/
def freeSlot : p0.TRef := .only

def directRef : Trm 0 :=
  .ref freeSlot .same

def capturedRef : AST 0 .trm :=
  .val (.fn .TLit (.mk (λ _ => .ref freeSlot (.lower .same))))

def capturedRefOnFalse : AST 0 .trm :=
  .apply capturedRef (.val (.lit bFalse))

end FreeCapture

namespace TypeHinted

def hintedFalse : AST 0 .trm :=
  .val (.lit bFalse)

def hintedIdFn : AST 0 .trm :=
  .val (.fn .TLit (.mk (λ proxy => .ref proxy .same)))

def hintedIdFnOnFalse : AST 0 .trm :=
  .apply hintedIdFn hintedFalse

end TypeHinted

namespace Malformed

def applyIdFnOnItself : AST 0 .trm :=
  .apply primitiveIdFn primitiveIdFn

def idFnOnFalse2 : AST 0 .trm :=
  .apply applyIdFnOnItself vFalse

def primitiveApply : AST 0 .trm :=
  .apply vFalse vTrue

def apply1 : AST 0 .trm :=
  .apply (.apply primitiveIdFn vFalse) vTrue

end Malformed

end Trm

end Tests.STLC.Sanity
