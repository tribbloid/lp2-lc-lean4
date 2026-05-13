import «Lp2lc».Active.DTLC.Def

namespace Tests.DTLC.Sanity
open Lp2lc.Active.DTLC

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
