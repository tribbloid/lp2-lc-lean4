import «Tests».STLC.ValDemo

namespace Tests.STLC.Sanity

open Lp2lc.Active.STLC
open Lp2lc.Active.Util
open Tests.STLC.Sanity.Symbolic

def bFalse : Lp2lc.Active.Util.CtxEmbedding.DeBruijn.B := "false"

def bTrue : Lp2lc.Active.Util.CtxEmbedding.DeBruijn.B := "true"

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
        .val (.fn .TLit (.mk (λ _ => AST.ref (.inl first)))))))

def get2nd : Trm :=
  .val
    (.fn .TLit
      (.mk (λ _ =>
        .val (.fn .TLit (.mk (λ second => AST.ref second))))))

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
def freeSlot : CtxEmbedding.DeBruijn.TRef := .only

def directRef : AST.Trm CtxEmbedding.DeBruijn.toParameters.Next :=
  AST.ref (.inl freeSlot)

def capturedRef : AST.Trm CtxEmbedding.DeBruijn.toParameters :=
  .val (.fn .TLit (.mk (λ _ => AST.ref (.inl freeSlot))))

def capturedRefOnFalse : Trm :=
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
