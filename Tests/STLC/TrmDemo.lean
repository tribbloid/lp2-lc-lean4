import «Tests».STLC.ValDemo

namespace Tests.STLC.Sanity

open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

def bFalse : I.B := "false"

def bTrue : I.B := "true"

namespace Trm

def vFalse : Trm :=
  .val (.lit bFalse)

def vTrue : Trm :=
  .val (.lit bTrue)

def primitiveIdFn : Trm :=
  .val (.fn .TLit (.mk (λ proxy => .ref proxy)))

def primitiveIdFnOnFalse : Trm :=
  .apply primitiveIdFn vFalse

def get1st : Trm :=
  .val
    (.fn .TLit
      (.mk (λ first =>
        .val (.fn .TLit (.mk (λ _ => AST.ref (P := I) (c := .root) first))))))

def get2nd : Trm :=
  .val
    (.fn .TLit
      (.mk (λ _ =>
        .val (.fn .TLit (.mk (λ second => AST.ref (P := I) (c := .extended) second))))))

def get1stOnTuple : Trm :=
  .apply (.apply get1st vFalse) vTrue

def get2ndOnTuple : Trm :=
  .apply (.apply get2nd vFalse) vTrue

def primitiveTrueFn : Trm :=
  .val (.fn .TLit (.mk (λ _ => .val (.lit bTrue))))

def primitiveTrueFnOnFalse : Trm :=
  .apply primitiveTrueFn vFalse

namespace FreeCapture

/-- A symbolic outer-context slot used by the syntax-only capture examples. -/
def freeSlot : Lp2lc.Active.Util.Parameters.Proxy I .root := .only

def directRef : AST.Trm (P := I) .extended :=
  AST.ref (P := I) (c := .root) freeSlot

def capturedRef : AST.Trm (P := I) .extended :=
  .val (.fn .TLit (.mk (λ _ => AST.ref (P := I) (c := .root) freeSlot)))

def capturedRefOnFalse : AST.Trm (P := I) .extended :=
  .apply capturedRef (.val (.lit bFalse))

end FreeCapture

namespace TypeHinted

def hintedFalse : Trm :=
  .val (.lit bFalse)

def hintedIdFn : Trm :=
  .val (.fn .TLit (.mk (λ proxy => .ref proxy)))

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
  .apply (.apply primitiveIdFn vFalse) vTrue

end Malformed

end Trm

end Tests.STLC.Sanity
