import «Lp2lc».Active.DTLC.DTLCDef

namespace Tests.DTLC.Sanity
open Lp2lc.Active.DTLC
open Lp2lc.Active.DTLC.Symbolic

namespace Typ

def false : Typ String :=
  .primitive

def idFn : Typ String :=
  .depFn .primitive (fun _x => .primitive)

def get1st : Typ String :=
  .depFn .primitive (fun _x =>
    .depFn .primitive (fun _y => .primitive))

def apply1stOn2ndFn : Typ String :=
  .depFn
    (.depFn .primitive (fun _x => .primitive))
    (fun _f =>
      .depFn .primitive (fun _x => .primitive))

end Typ


end Sanity
