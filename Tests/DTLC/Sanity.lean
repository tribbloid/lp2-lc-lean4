import «Lp2lc».Active.DTLC.Def



/-
this is a supporting sanity test file for DOT calculus syntax definition.

each of the AST below are supposed to represent scala variable of the same name
in @SanityExample.scala
-/

namespace Tests.DTLC.Sanity
open Lp2lc.Active.DTLC

instance : DecidableEq Lp2lc.Active.Util.ByteCode :=
  String.decEq

abbrev Handle := Nat

abbrev TypAST := Typ Handle

abbrev ValAST := Val Handle

abbrev TrmAST := Trm Handle

namespace Val

def idFn : ValAST :=
  .fn (body := fun x => .ref x)

def handle : ValAST -> Handle
| .primitive "false" =>
  0
| .primitive "true" =>
  1
| .primitive _ =>
  3
| .fn _ =>
  2

end Val

instance : FBound Handle where
  beq := Nat.beq
  fwd := Val.handle

namespace Trm

def false : TrmAST :=
  .val (.primitive "false")

def true : TrmAST :=
  .val (.primitive "true")

def idFn : TrmAST :=
  .val (.fn (body := fun x => .ref x))

def idFnOnFalse : TrmAST :=
  .depApply idFn false

example :
    idFnOnFalse =
      .depApply idFn false := rfl

def get1st : TrmAST :=
  .val
    (.fn (body := fun x =>
      .val
        (.fn (body := fun _y => .ref x))))

def get2nd : TrmAST :=
  .val
    (.fn (body := fun _x =>
      .val
        (.fn (body := fun y => .ref y))))

def get1stOnTuple : TrmAST :=
  .depApply
    (.depApply get1st false)
    true

def get2ndOnTuple : TrmAST :=
  .depApply
    (.depApply get2nd false)
    true

example :
    get2ndOnTuple =
      .depApply (.depApply get2nd false) true := rfl

def apply1stOn2ndFn : TrmAST :=
  .val (.fn (body := fun f =>
      .val (.fn (body := fun x =>
        .depApply
          (.ref f)
          (.ref x)))))

def apply1stOn2ndFnOnTuple : TrmAST :=
  .depApply
    (.depApply apply1stOn2ndFn idFn)
    false

example :
    apply1stOn2ndFnOnTuple =
      .depApply
        (.depApply apply1stOn2ndFn idFn)
        false := rfl

def applyidFnOnItself : TrmAST :=
  .depApply idFn idFn

def idFnOnFalse2 : TrmAST :=
  .depApply applyidFnOnItself false

def malformedPrimitiveApply : TrmAST :=
  .depApply false true

end Trm

namespace Typ

def false : TypAST :=
  .primitive

def idFn : TypAST :=
  .depFn .primitive (fun _x => .primitive)

def get1st : TypAST :=
  .depFn .primitive (fun _x =>
    .depFn .primitive (fun _y => .primitive))

def apply1stOn2ndFn : TypAST :=
  .depFn
    (.depFn .primitive (fun _x => .primitive))
    (fun _f =>
      .depFn .primitive (fun _x => .primitive))

end Typ

namespace Eval

attribute [local simp] Trm.eval Trm.false Trm.true Trm.idFn Trm.idFnOnFalse
attribute [local simp] Trm.get1st Trm.get2nd Trm.get1stOnTuple Trm.get2ndOnTuple
attribute [local simp] Trm.apply1stOn2ndFn Trm.apply1stOn2ndFnOnTuple
attribute [local simp] Trm.applyidFnOnItself Trm.idFnOnFalse2
attribute [local simp] Val.handle FBound.fwd
attribute [local simp] Trm.subst_ref Val.subst_ref

example : Trm.false.eval 0 = .outOfFuel := rfl
example : Trm.false.eval 1 = .some (.primitive "false") := rfl
example : Trm.false.eval 2 = .some (.primitive "false") := rfl
example : Trm.idFnOnFalse.eval 0 = .outOfFuel := rfl

example : Trm.idFnOnFalse.eval 2 =
    .some (.primitive "false") := by
  simp

example : Trm.get1stOnTuple.eval 1 = .outOfFuel := rfl

example : Trm.get1stOnTuple.eval 3 =
    .some (.primitive "false") := by
  simp

example : Trm.get2ndOnTuple.eval 3 =
    .some (.primitive "true") := by
  simp

example : Trm.apply1stOn2ndFnOnTuple.eval 2 = .outOfFuel := rfl

example : Trm.apply1stOn2ndFnOnTuple.eval 4 =
    .some (.primitive "false") := by
  simp

example : Trm.applyidFnOnItself.eval 0 = .outOfFuel := rfl

example : Trm.applyidFnOnItself.eval 2 =
    .some Val.idFn := by
  simp [Val.idFn]

example : Trm.idFnOnFalse2.eval 1 = .outOfFuel := rfl

example : Trm.idFnOnFalse2.eval 3 =
    .some (.primitive "false") := by
  simp

example : Trm.malformedPrimitiveApply.eval 0 = .outOfFuel := rfl

example : Trm.malformedPrimitiveApply.eval 1 = .outOfFuel := rfl

example : Trm.malformedPrimitiveApply.eval 2 = .error := rfl

end Eval

-- namespace Eval

-- example : Definitional.eval Trm.idFnOnFalse 0 = none := rfl

-- example :
--     Definitional.eval Trm.idFnOnFalse 1 =
--       some ((Val.primitive "false") : Val PUnit) := rfl

-- example :
--     Denotational.eval Trm.idFnOnFalse 1 =
--       some ((Val.primitive "false") : Val PUnit) := rfl

-- example : Definitional.eval Trm.get1stOnTuple 1 = none := rfl

-- example :
--     Definitional.eval Trm.get1stOnTuple 2 =
--       some ((Val.primitive "false") : Val PUnit) := rfl

-- example :
--     Denotational.eval Trm.get2ndOnTuple 2 =
--       some ((Val.primitive "true") : Val PUnit) := rfl

-- example : Definitional.eval Trm.apply1stOn2ndFnOnTuple 2 = none := rfl

-- example :
--     Definitional.eval Trm.apply1stOn2ndFnOnTuple 3 =
--       some ((Val.primitive "false") : Val PUnit) := rfl

-- example : Definitional.eval (.depApply Trm.idFn Trm.idFn) 1 = none := rfl

-- end Eval

-- namespace Typing

-- example : TrmClosed.typing Trm.false 2 Typ.false := by
--   simp [TrmClosed.typing, Trm.false, Typ.false]

-- example : TrmClosed.typing Trm.true 2 Typ.true := by
--   simp [TrmClosed.typing, Trm.true, Typ.true]

-- example : TrmClosed.typing Trm.idFn 3 Typ.idFn := by
--   simp [TrmClosed.typing, Trm.idFn, Typ.idFn]

-- example : TrmClosed.typing Trm.get1st 4 Typ.get1st := by
--   simp [TrmClosed.typing, Trm.get1st, Typ.get1st]

-- example : TrmClosed.typing Trm.get2nd 4 Typ.get2nd := by
--   simp [TrmClosed.typing, Trm.get2nd, Typ.get2nd]

-- example : ¬ TrmClosed.typing Trm.apply1stOn2ndFnOnTuple 6 Typ.apply1stOn2ndFnOnTuple := by
--   simp [TrmClosed.typing, Trm.apply1stOn2ndFnOnTuple, Trm.apply1stOn2ndFn, Trm.idFn,
--     Trm.false,
--     Typ.apply1stOn2ndFnOnTuple]

-- end Typing


end Sanity
