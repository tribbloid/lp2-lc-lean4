import «Tests».STLC.ValDemo

namespace Tests.STLC.Sanity

open Lp2lc.Active.STLC
open Lp2lc.Active.Util

def bFalse : Lp2lc.Active.Util.CtxEmbedding.DeBruijn.B := "false"

def bTrue : Lp2lc.Active.Util.CtxEmbedding.DeBruijn.B := "true"

namespace Trm

def vFalse : AST .trm :=
  .val (.lit bFalse)

def vTrue : AST .trm :=
  .val (.lit bTrue)

def primitiveIdFn : AST .trm :=
  .val (.fn .TLit (.mk (λ proxy => .ref proxy)))

def primitiveIdFnOnFalse : AST .trm :=
  .apply primitiveIdFn vFalse

def get1st : AST .trm :=
  .val
    (.fn .TLit
      (.mk (λ first =>
        .val (.fn .TLit (.mk (λ _ => .ref (.inl first)))))))

def get2nd : AST .trm :=
  .val
    (.fn .TLit
      (.mk (λ _ =>
        .val (.fn .TLit (.mk (λ second => .ref second))))))

def get1stOnTuple : AST .trm :=
  .apply (.apply get1st vFalse) vTrue

def get2ndOnTuple : AST .trm :=
  .apply (.apply get2nd vFalse) vTrue

def primitiveTrueFn : AST .trm :=
  .val (.fn .TLit (.mk (λ _ => .val (.lit bTrue))))

def primitiveTrueFnOnFalse : AST .trm :=
  .apply primitiveTrueFn vFalse

namespace FreeCapture

/-- A symbolic outer-context slot used by the syntax-only capture examples. -/
def freeSlot : CtxEmbedding.DeBruijn.TRef := .only

def directRef : Pre.AST CtxEmbedding.DeBruijn.toParameters.Next .trm :=
  .ref (.inl freeSlot)

def capturedRef : AST .trm :=
  .val (.fn .TLit (.mk (λ _ => .ref (.inl freeSlot))))

def capturedRefOnFalse : AST .trm :=
  .apply capturedRef (.val (.lit bFalse))

end FreeCapture

namespace TypeHinted

def hintedFalse : AST .trm :=
  .val (.lit bFalse)

def hintedIdFn : AST .trm :=
  .val (.fn .TLit (.mk (λ proxy => .ref proxy)))

def hintedIdFnOnFalse : AST .trm :=
  .apply hintedIdFn hintedFalse

end TypeHinted

namespace Malformed

def applyIdFnOnItself : AST .trm :=
  .apply primitiveIdFn primitiveIdFn

def idFnOnFalse2 : AST .trm :=
  .apply applyIdFnOnItself vFalse

def primitiveApply : AST .trm :=
  .apply vFalse vTrue

def apply1 : AST .trm :=
  .apply (.apply primitiveIdFn vFalse) vTrue

end Malformed

end Trm

end Tests.STLC.Sanity
