import «Lp2lc».Active.STLC.Serial.Eval
import «Tests».STLC.TrmDemo

namespace Tests.STLC.Sanity.Trm

open Lp2lc.Active.Util Lp2lc.Active.STLC

section eval

private abbrev _root_.Lp2lc.Active.STLC.Trm.evalShouldYield {n} (trm : Trm n) (fuel : Nat)
    (expected : Return Val) -- TODO: type of it should be `(expected : Val)`, if result is ".corrupted", should use `evalShouldCrash`
    (bindings : ExeBindings := .empty) : Prop :=
  returnsValue (trm.eval bindings) fuel expected

-- TODO: imiplement this & add document
private abbrev _root_.Lp2lc.Active.STLC.Trm.evalShouldCrash {n} (trm : Trm n) (fuel : Nat)
    (bindings : ExeBindings := .empty) : Prop := sorry

-- TODO: the fuck is this? why calling with long prefix while dot-notation can be used?
-- TODO: Also augment docstring of evalShouldYield and evalShouldCrash such that they can only be invoked using dot-notation
#guard vFalse._root_.Lp2lc.Active.STLC.Trm.evalShouldYield 1 (.some falseValue)

#guard primitiveIdFn._root_.Lp2lc.Active.STLC.Trm.evalShouldYield 1 (.some Val.idFn)

-- A nested identity is closed; a function returning its captured argument is not an identity.
#guard returnsValue (AST.eval (.apply get2nd vFalse : Trm)) 2 (.some Val.idFn)
#guard ¬ get1stOnFalse._root_.Lp2lc.Active.STLC.Trm.evalShouldYield 2 (.some Val.idFn)

#guard primitiveIdFnOnFalse._root_.Lp2lc.Active.STLC.Trm.evalShouldYield 2 (.some falseValue)

#guard get1stOnTuple._root_.Lp2lc.Active.STLC.Trm.evalShouldYield 3 (.some falseValue)

#guard get2ndOnTuple._root_.Lp2lc.Active.STLC.Trm.evalShouldYield 3 (.some trueValue)

#guard higherOrderApplication._root_.Lp2lc.Active.STLC.Trm.evalShouldYield 4 (.some falseValue)

#guard Malformed.WrongTIn.eval.shouldFail 3

#guard Malformed.ContainWrongTIn.eval.shouldFail 4

#guard Malformed.wrongNestedTIn.eval.shouldFail 4

#guard Malformed.applyLit2.eval.shouldFail 3

#guard Malformed.applyLit1.eval.shouldFail 2

#guard Malformed.applyLitToApplication.eval.shouldFail 3

#guard primitiveTrueFnOnFalse._root_.Lp2lc.Active.STLC.Trm.evalShouldYield 2 (.some trueValue)

#guard primitiveLiteralIdFnOnFalse._root_.Lp2lc.Active.STLC.Trm.evalShouldYield 2 (.some falseValue)

#guard primitiveFirstFnOnTuple._root_.Lp2lc.Active.STLC.Trm.evalShouldYield 3 (.some falseValue)

#guard Corrupted.primitiveFnOnTuple._root_.Lp2lc.Active.STLC.Trm.evalShouldYield 3 .corrupted

#guard Corrupted.corruptApplication._root_.Lp2lc.Active.STLC.Trm.evalShouldYield 2 .corrupted

#guard match Corrupted.corruptApplication.eval .empty 1000 with
  | .yield (some .corrupted) => true
  | _ => false

#guard Corrupted.corruptedCallee._root_.Lp2lc.Active.STLC.Trm.evalShouldYield 3 .corrupted

#guard Corrupted.corruptedArgument._root_.Lp2lc.Active.STLC.Trm.evalShouldYield 3 .corrupted

#guard Corrupted.corruptedBody._root_.Lp2lc.Active.STLC.Trm.evalShouldYield 3 .corrupted

#guard Corrupted.illTypedPrimitiveResult._root_.Lp2lc.Active.STLC.Trm.evalShouldYield 4 .corrupted

#guard Malformed.primitiveLiteralIdFnOnFn.eval.shouldFail 2

end eval

end Tests.STLC.Sanity.Trm
