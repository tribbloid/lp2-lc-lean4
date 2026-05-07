import «Lp2lc».Active.DTLC.Def



/-
this is a supporting sanity test file for DOT calculus syntax definition.

each of the AST below are supposed to represent scala variable of the same name
in @SanityExample.scala
-/

namespace Tests.DTLC.Sanity
open Lp2lc.Active.DTLC

namespace Val

def idFn : ValAST :=
  .depFn (body := fun x => Correspondence.rev x)

end Val

namespace Trm

def false : TrmAST :=
  .val (.primitive "false")

def true : TrmAST :=
  .val (.primitive "true")

def idFn : TrmAST :=
  .val (.depFn (body := fun x => Correspondence.rev x))

def idFnOnFalse : TrmAST :=
  .depApply idFn false

example {I : Index} [Correspondence I] :
    (idFnOnFalse : Trm I) =
      .depApply (idFn : Trm I) (false : Trm I) := rfl

def get1st : TrmAST :=
  .val
    (.depFn (body := fun x =>
      .val
        (.depFn (body := fun _y => Correspondence.rev x))))

def get2nd : TrmAST :=
  .val
    (.depFn (body := fun _x =>
      .val
        (.depFn (body := fun y => Correspondence.rev y))))

def get1stOnTuple : TrmAST :=
  .depApply
    (.depApply get1st false)
    true

def get2ndOnTuple : TrmAST :=
  .depApply
    (.depApply get2nd false)
    true

example {I : Index} [Correspondence I] :
    (get2ndOnTuple : Trm I) =
      .depApply (.depApply (get2nd : Trm I) (false : Trm I)) (true : Trm I) := rfl

def apply1stOn2ndFn : TrmAST :=
  .val (.depFn (body := fun f =>
      .val (.depFn (body := fun x =>
        .depApply
          (Correspondence.rev f)
          (Correspondence.rev x)))))

def apply1stOn2ndFnOnTuple : TrmAST :=
  .depApply
    (.depApply apply1stOn2ndFn idFn)
    false

example {I : Index} [Correspondence I] :
    (apply1stOn2ndFnOnTuple : Trm I) =
      .depApply
        (.depApply (apply1stOn2ndFn : Trm I) (idFn : Trm I))
        (false : Trm I) := rfl

def applyidFnOnItself : TrmAST :=
  .depApply idFn idFn

def idFnOnFalse2 : TrmAST :=
  .depApply applyidFnOnItself false

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
