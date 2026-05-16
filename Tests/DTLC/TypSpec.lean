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


end Sanity
