import «Lp2lc».Active.DTLC.Impl

namespace Tests.DTLC.Sanity
open Lp2lc.Active.DTLC
open Lp2lc.Active.DTLC.Symbolic

namespace Typ

def false : Typ :=
  .primitive

def idFn : Typ :=
  .depFn .primitive (fun _x => .primitive)

def get1st : Typ :=
  .depFn .primitive (fun _x =>
    .depFn .primitive (fun _y => .primitive))

def apply1stOn2ndFn : Typ :=
  .depFn
    (.depFn .primitive (fun _x => .primitive))
    (fun _f =>
      .depFn .primitive (fun _x => .primitive))

end Typ


end Sanity
