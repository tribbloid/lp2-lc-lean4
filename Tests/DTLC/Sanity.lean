import «Lp2lc».Active.DTLC.Def



/-
this is a supporting sanity test file for DOT calculus syntax definition.

each of the AST below are supposed to represent scala variable of the same name
in @SanityExample.scala
-/

namespace Tests.DTLC.Sanity
open Lp2lc.Active.DTLC

namespace Typ

def false : TypClosed :=
  .primitive

def idFn : TypClosed :=
  .depFn .primitive (fun _x => .primitive)

def get1st : TypClosed :=
  .depFn .primitive (fun _x =>
    .depFn .primitive (fun _y => .primitive))

def apply1stOn2ndFn : TypClosed :=
  .depFn
    (.depFn .primitive (fun _x => .primitive))
    (fun _f =>
      .depFn .primitive (fun _x => .primitive))

end Typ

namespace Trm

section
variable (ref : {I : Index} -> (I -> Val I))

def false : TrmClosed :=
  .val (.primitive "false")

def true : TrmClosed :=
  .val (.primitive "true")

def idFn : TrmClosed :=
  .val
    (.depFn (body := fun x => .val (ref x)))

def idFnOnFalse : TrmClosed :=
  .depApply (idFn ref) false

example : idFnOnFalse.pretty 3 = "((fun x_1 => x_1) false)" := rfl

def get1st : TrmClosed :=
  .val
    (.depFn (body := fun x =>
      .val
        (.depFn (body := fun _y => .val (Val.ref x)))))

def get2nd : TrmClosed :=
  .val
    (.depFn (body := fun _x =>
      .val
        (.depFn (body := fun y => .val (Val.ref y)))))

def get1stOnTuple : TrmClosed :=
  .depApply
    (.depApply get1st false)
    true

def get2ndOnTuple : TrmClosed :=
  .depApply
    (.depApply get2nd false)
    true

example :
    get2ndOnTuple.pretty 5 =
      "(((fun x_2 => (fun x_1 => x_1)) false) true)" := rfl

def apply1stOn2ndFn : TrmClosed :=
  .val (.depFn (body := fun f =>
      .val (.depFn (body := fun x =>
        .depApply
          (.val (Val.ref f))
          (.val (Val.ref x))))))

def apply1stOn2ndFnOnTuple : TrmClosed :=
  .depApply
    (.depApply apply1stOn2ndFn idFn)
    false

example :
    apply1stOn2ndFnOnTuple.pretty 6 =
      "(((fun x_3 => (fun x_2 => (x_3 x_2))) (fun x_3 => x_3)) false)" := rfl

def applyidFnOnItself : TrmClosed :=
  .depApply Trm.idFn Trm.idFn

def idFnOnFalse2 : TrmClosed :=
  .depApply applyidFnOnItself false

end Trm

namespace Runtime


end Runtime

-- namespace Eval

-- example : Trm.false.eval 0 = none := rfl
-- example : Trm.false.eval 1 = some ((Val.primitive "false") : Val SemanticCarrier) := rfl
-- example : Trm.false.eval 2 = some ((Val.primitive "false") : Val SemanticCarrier) := rfl
-- example : Trm.idFnOnFalse.eval 0 = none := rfl
-- example : Trm.idFnOnFalse.eval 2 = some ((Val.primitive "false") : Val SemanticCarrier) := rfl
-- example : Trm.get1stOnTuple.eval 1 = none := rfl
-- example : Trm.get1stOnTuple.eval 3 = some ((Val.primitive "false") : Val SemanticCarrier) := rfl
-- example : Trm.get2ndOnTuple.eval 3 = some ((Val.primitive "true") : Val SemanticCarrier) := rfl
-- example : Trm.apply1stOn2ndFnOnTuple.eval 2 = none := rfl
-- example : Trm.apply1stOn2ndFnOnTuple.eval 4 = some ((Val.primitive "false") : Val SemanticCarrier) := rfl
-- example : (Trm.applyidFnOnItself.eval 0).isNone = true := rfl
-- example : (Trm.applyidFnOnItself.eval 2).isSome = true := rfl
-- example : Trm.idFnOnFalse2.eval 1 = none := rfl
-- example : Trm.idFnOnFalse2.eval 3 = some ((Val.primitive "false") : Val SemanticCarrier) := rfl

-- end Eval

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
