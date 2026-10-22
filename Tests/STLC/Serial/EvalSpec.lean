import «Lp2lc».Active.STLC.Serial.Eval
import «Tests».STLC.TrmDemo

namespace Tests.STLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.STLC

section eval

private def evalAt {n} (trm : Trm n) (fuel : Nat) (bindings : ExeBindings := .empty) :=
  (trm.eval bindings fuel, trm.eval bindings (fuel - 1))

private def freeBindings : ExeBindings := NatBindings.empty.set 0 ⟨0, .lit bTrue, .empty⟩

example : evalAt vFalse 1 =
    (.yield (some (.some ⟨0, .lit bFalse, .empty⟩)), .outOfFuel) := rfl

example : evalAt primitiveIdFnOnFalse 2 =
    (.yield (some (.some ⟨0, .lit bFalse, .empty⟩)), .outOfFuel) := rfl

example : evalAt get1stOnTuple 3 =
    (.yield (some (.some ⟨0, .lit bFalse, .empty⟩)), .outOfFuel) := rfl

example : evalAt get2ndOnTuple 3 =
    (.yield (some (.some ⟨0, .lit bTrue, .empty⟩)), .outOfFuel) := rfl

example : evalAt Malformed.WrongTypeIdFnOnItself 2 =
    (.yield (some (.some ⟨0, Val.idFn, .empty⟩)), .outOfFuel) := rfl

example : evalAt Malformed.WrongTypeIdFnOnFalse2 3 =
    (.yield (some (.some ⟨0, .lit bFalse, .empty⟩)), .outOfFuel) := rfl

#guard Trm.Malformed.applyLit2.eval.shouldFail 3

#guard Trm.Malformed.applyLit1.eval.shouldFail 2

example : evalAt primitiveTrueFnOnFalse 2 =
    (.yield (some (.some ⟨1, .lit bTrue, NatBindings.empty.set 1 ⟨0, .lit bFalse, .empty⟩⟩)),
      .outOfFuel) := rfl

example : evalAt FreeCapture.directRef 1 freeBindings =
    (.yield (some (.some ⟨0, .lit bTrue, .empty⟩)), .outOfFuel) := rfl

example : evalAt FreeCapture.capturedRefOnFalse 2 freeBindings =
    (.yield (some (.some ⟨0, .lit bTrue, .empty⟩)), .outOfFuel) := rfl

end eval

end Trm

end Sanity
