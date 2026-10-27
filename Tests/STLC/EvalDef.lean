import «Tests».STLC.TrmDemo
import «Lp2lc».Active.STLC.Hash

namespace Tests.STLC.Sanity

open Lp2lc.Active.STLC Lp2lc.Active.Util

def falseValue : ExeVal := ⟨0, .lit bFalse, .empty⟩
def trueValue : ExeVal := ⟨0, .lit bTrue, .empty⟩
def freeBindings : ExeBindings := NatBindings.empty.set 0 trueValue
def capturedTrueValue : ExeVal := ⟨1, .lit bTrue, NatBindings.empty.set 1 falseValue⟩

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

-- Exercise the same captured primitive with each evaluator, including its missing-capture failure.
def capturedPrimitiveCase (check : Trm 0 → Trm 0 → ExeBindings → Bool) : Bool :=
  match Trm.FreeCapture.capturedRef with
  | .val value =>
    let primitive : Val := .fnPrimitive (.TFn .TLit .TLit) (λ _ => value)
    let caller := NatBindings.empty.set 0 (⟨0, primitive, freeBindings⟩ : ExeVal)
    check (.apply (.apply Trm.FreeCapture.directRef Trm.vFalse) Trm.vFalse)
      (.apply (.val primitive) Trm.vFalse) caller
  | _ => false

namespace Trm

def primitiveLiteralIdFn : Trm :=
  .val (.fnPrimitive .TLit .lit)

def primitiveLiteralIdFnOnFalse : Trm :=
  .apply primitiveLiteralIdFn vFalse

def primitiveFirstFnOnTuple : Trm :=
  .apply
    (.apply (.val (.fnPrimitive (.TFn .TLit .TLit)
      (λ first => .fnPrimitive .TLit (λ _ => .lit first)))) vFalse) vTrue

namespace Malformed

def primitiveLiteralIdFnOnFn : Trm :=
  .apply primitiveLiteralIdFn primitiveIdFn

def primitiveFnOnTuple : Trm :=
  .apply
    (.apply (.val (.fnPrimitive (.TFn .TLit .TLit)
      (λ _ => .fnPrimitive .TLit (λ _ => Val.idFn)))) vFalse) vTrue

end Malformed

end Trm

end Tests.STLC.Sanity
