import «Lp2lc».Active.DTLC.Def



/-
this is a supporting sanity test file for DOT calculus syntax definition.

each of the AST below are supposed to represent scala variable of the same name
in @SanityExample.scala
-/

namespace Tests.DTLC.Sanity
open Lp2lc.Active.DTLC

class FIso (I : Index) extends FBound I where
  rev : I -> Val I
  rev_fwd : (value : Val I) -> rev (fwd value) = value

attribute [simp] FIso.rev_fwd

abbrev TypAST := {I : Index} -> [FIso I] -> Typ I

abbrev ValAST := {I : Index} -> [FIso I] -> Val I

abbrev TrmAST := {I : Index} -> [FIso I] -> Trm I

namespace Val

def idFn : ValAST :=
  .fn (body := fun x => FIso.rev x)

end Val

namespace Trm

def false : TrmAST :=
  .val (.primitive "false")

def true : TrmAST :=
  .val (.primitive "true")

def idFn : TrmAST :=
  .val (.fn (body := fun x => FIso.rev x))

def idFnOnFalse : TrmAST :=
  .depApply idFn false

example {I : Index} [FIso I] :
    (idFnOnFalse : Trm I) =
      .depApply (idFn : Trm I) (false : Trm I) := rfl

def get1st : TrmAST :=
  .val
    (.fn (body := fun x =>
      .val
        (.fn (body := fun _y => FIso.rev x))))

def get2nd : TrmAST :=
  .val
    (.fn (body := fun _x =>
      .val
        (.fn (body := fun y => FIso.rev y))))

def get1stOnTuple : TrmAST :=
  .depApply
    (.depApply get1st false)
    true

def get2ndOnTuple : TrmAST :=
  .depApply
    (.depApply get2nd false)
    true

example {I : Index} [FIso I] :
    (get2ndOnTuple : Trm I) =
      .depApply (.depApply (get2nd : Trm I) (false : Trm I)) (true : Trm I) := rfl

def apply1stOn2ndFn : TrmAST :=
  .val (.fn (body := fun f =>
      .val (.fn (body := fun x =>
        .depApply
          (FIso.rev f)
          (FIso.rev x)))))

def apply1stOn2ndFnOnTuple : TrmAST :=
  .depApply
    (.depApply apply1stOn2ndFn idFn)
    false

example {I : Index} [FIso I] :
    (apply1stOn2ndFnOnTuple : Trm I) =
      .depApply
        (.depApply (apply1stOn2ndFn : Trm I) (idFn : Trm I))
        (false : Trm I) := rfl

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

variable {I : Index} [FIso I]

attribute [local simp] Trm.eval Trm.false Trm.true Trm.idFn Trm.idFnOnFalse
attribute [local simp] Trm.get1st Trm.get2nd Trm.get1stOnTuple Trm.get2ndOnTuple
attribute [local simp] Trm.apply1stOn2ndFn Trm.apply1stOn2ndFnOnTuple
attribute [local simp] Trm.applyidFnOnItself Trm.idFnOnFalse2

example : ((Trm.false : Trm I).eval 0) = none := rfl
example : ((Trm.false : Trm I).eval 1) = some ((Val.primitive "false") : Val I) := rfl
example : ((Trm.false : Trm I).eval 2) = some ((Val.primitive "false") : Val I) := rfl
example : ((Trm.idFnOnFalse : Trm I).eval 0) = none := rfl

example : ((Trm.idFnOnFalse : Trm I).eval 2) =
    some ((Val.primitive "false") : Val I) := by
  simp

example : ((Trm.get1stOnTuple : Trm I).eval 1) = none := rfl

example : ((Trm.get1stOnTuple : Trm I).eval 3) =
    some ((Val.primitive "false") : Val I) := by
  simp

example : ((Trm.get2ndOnTuple : Trm I).eval 3) =
    some ((Val.primitive "true") : Val I) := by
  simp

example : ((Trm.apply1stOn2ndFnOnTuple : Trm I).eval 2) = none := rfl

example : ((Trm.apply1stOn2ndFnOnTuple : Trm I).eval 4) =
    some ((Val.primitive "false") : Val I) := by
  simp

example : (((Trm.applyidFnOnItself : Trm I).eval 0).isNone) = true := rfl

example : (((Trm.applyidFnOnItself : Trm I).eval 2).isSome) = true := by
  simp

example : ((Trm.idFnOnFalse2 : Trm I).eval 1) = none := rfl

example : ((Trm.idFnOnFalse2 : Trm I).eval 3) =
    some ((Val.primitive "false") : Val I) := by
  simp

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
