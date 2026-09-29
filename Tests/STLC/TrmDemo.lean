import «Lp2lc».Active.STLC.Eval
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
        .val (.fn .TLit (.mk (λ _ => AST.ref (source := 1) first))))))

def get2nd : Trm :=
  .val
    (.fn .TLit
      (.mk (λ _ =>
        .val (.fn .TLit (.mk (λ second => AST.ref (source := 2) second))))))

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
def freeSlot : Lp2lc.Active.Util.CtxEmbedding.Proxy Lp2lc.Active.Util.CtxEmbedding.DeBruijn 0 := .only

def directRef : AST.Trm (AST.At 1) :=
  AST.ref (source := 0) freeSlot

def capturedRef : AST.Trm (AST.At 0) :=
  .val (.fn .TLit (.mk (λ _ => AST.ref (source := 0) freeSlot)))

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

section eval

private def literalResult (result : Rec.Outcome (Option RuntimeValue)) : Option String :=
  match result with
  | .yield (some (RuntimeValue.mk _ (Pre.AST.lit repr) _)) => some repr
  | _ => none

private def outerValue : RuntimeValue := .mk 0 (.lit "outer") (λ _ => none)
private def knownBindings : Bindings := λ slot => if slot = 0 then some outerValue else none

example : literalResult (AST.Trm.eval Trm.primitiveIdFnOnFalse (λ _ => none) 2) = some "false" := rfl
example : literalResult (AST.Trm.eval Trm.get1stOnTuple (λ _ => none) 3) = some "false" := rfl
example : literalResult (AST.Trm.eval Trm.get2ndOnTuple (λ _ => none) 3) = some "true" := rfl
example : literalResult (AST.Trm.eval Trm.FreeCapture.directRef knownBindings 1) = some "outer" := rfl
example : literalResult (AST.Trm.eval Trm.FreeCapture.capturedRefOnFalse knownBindings 2) = some "outer" := rfl

end eval

end Tests.STLC.Sanity
