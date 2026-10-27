import «Tests».STLC.ValDemo
import «Lp2lc».Active.STLC.Hash

namespace Tests.STLC.Sanity

open Lp2lc.Active.STLC
open Lp2lc.Active.Util

def bFalse := "false"

def bTrue := "true"

def falseValue : ExeVal := ⟨0, .lit bFalse, .empty⟩
def trueValue : ExeVal := ⟨0, .lit bTrue, .empty⟩
def freeBindings : ExeBindings := NatBindings.empty.set 0 trueValue

open Lean (Json toJson)

-- Compare runtime closures, including their contexts and captured bindings, in evaluator tests.
def closureSignature (closure : ExeVal) : Json :=
  match closure with
  | .mk n value captured =>
    let rec bindings (entries : ExeBindings) : Json :=
      match entries with
      | .empty => .null
      | .set rest index value => .arr #[bindings rest, toJson index, closureSignature value]
    .arr #[toJson n, astToJson value toJson toJson, bindings captured]
termination_by structural closure

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

def primitiveFirstFnOnTuple : Trm :=
  .apply
    (.apply (.val (.fnPrimitive (.TFn .TLit .TLit)
      (λ first => .fnPrimitive .TLit (λ _ => .lit first)))) vFalse) vTrue

namespace FreeCapture

/-- A symbolic outer-context slot used by the syntax-only capture examples. -/
def freeSlot : IndexEncoding.SerialProxy 0 := .only

def directRef : Trm 0 :=
  .ref freeSlot .same

def capturedRefValue : Val :=
  .fn .TLit (.mk (λ _ => .ref freeSlot (.lower .same)))

def capturedRef : AST 0 .trm :=
  .val capturedRefValue

def primitive : Val :=
  .fnPrimitive (.TFn .TLit .TLit) (λ _ => capturedRefValue)

def primitiveCaller : ExeBindings := NatBindings.empty.set 0 ⟨0, primitive, freeBindings⟩

def primitiveOnFalse : Trm := .apply (.val primitive) vFalse

def primitiveTwiceOnFalse : Trm := .apply (.apply directRef vFalse) vFalse

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

def WrongTypeIdFnOnItself : AST 0 .trm :=
  .apply primitiveIdFn primitiveIdFn

def WrongTypeIdFnOnFalse2 : AST 0 .trm :=
  .apply WrongTypeIdFnOnItself vFalse

def applyLit1 : AST 0 .trm :=
  .apply vFalse vTrue

def applyLit2 : AST 0 .trm :=
  .apply (.apply primitiveIdFn vFalse) vTrue

def primitiveFnOnTuple : Trm :=
  .apply
    (.apply (.val (.fnPrimitive (.TFn .TLit .TLit)
      (λ _ => .fnPrimitive .TLit (λ _ => Val.idFn)))) vFalse) vTrue

end Malformed

end Trm

end Tests.STLC.Sanity
