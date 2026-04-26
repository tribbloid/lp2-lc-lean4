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

def identityFn : TypClosed :=
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

def false : TrmClosed :=
  .val (.primitive "false")

def true : TrmClosed :=
  .val (.primitive "true")

def identityFn : TrmClosed :=
  .val
    (.depFn (fun x => .var x))

def identityFnOnFalse : TrmClosed :=
  .depApply identityFn false

def get1st : TrmClosed :=
  .val
    (.depFn (fun x =>
      .val
        (.depFn (fun _y => .var x))))

def get2nd : TrmClosed :=
  .val
    (.depFn (fun _x =>
      .val
        (.depFn (fun y => .var y))))

def get1stOnTuple : TrmClosed :=
  .depApply
    (.depApply get1st false)
    true

def get2ndOnTuple : TrmClosed :=
  .depApply
    (.depApply get2nd false)
    true

def apply1stOn2ndFn : TrmClosed :=
  .val (.depFn (fun f =>
    .val (.depFn (fun x =>
      .depApply
        (.var f)
        (.var x)))))

def apply1stOn2ndFnOnTuple : TrmClosed :=
  .depApply
    (.depApply apply1stOn2ndFn identityFn)
    false

end Trm

namespace Eval

example : TrmClosed.eval Trm.identityFnOnFalse 1 = some (Val.primitive "false") := by
  sorry

example : TrmClosed.eval Trm.identityFnOnFalse 3 = some ((Val.primitive "false") : RuntimeVal) := by
  sorry

example : TrmClosed.eval Trm.get1stOnTuple 5 = some ((Val.primitive "false") : RuntimeVal) := by
  sorry

example : TrmClosed.eval Trm.get2ndOnTuple 5 = some ((Val.primitive "true") : RuntimeVal) := by
  sorry

example : TrmClosed.eval Trm.apply1stOn2ndFnOnTuple 6 = some (Val.primitive "false") := by
  sorry

end Eval

-- namespace Typing

-- example : TrmClosed.typing Trm.false 2 Typ.false := by
--   simp [TrmClosed.typing, Trm.false, Typ.false]

-- example : TrmClosed.typing Trm.true 2 Typ.true := by
--   simp [TrmClosed.typing, Trm.true, Typ.true]

-- example : TrmClosed.typing Trm.identityFn 3 Typ.identityFn := by
--   simp [TrmClosed.typing, Trm.identityFn, Typ.identityFn]

-- example : TrmClosed.typing Trm.get1st 4 Typ.get1st := by
--   simp [TrmClosed.typing, Trm.get1st, Typ.get1st]

-- example : TrmClosed.typing Trm.get2nd 4 Typ.get2nd := by
--   simp [TrmClosed.typing, Trm.get2nd, Typ.get2nd]

-- example : ¬ TrmClosed.typing Trm.apply1stOn2ndFnOnTuple 6 Typ.apply1stOn2ndFnOnTuple := by
--   simp [TrmClosed.typing, Trm.apply1stOn2ndFnOnTuple, Trm.apply1stOn2ndFn, Trm.identityFn,
--     Trm.false,
--     Typ.apply1stOn2ndFnOnTuple]

-- end Typing


end Sanity
