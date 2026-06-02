import «Lp2lc».Active.DTLC.Def

namespace Tests.DTLC.Sanity
open Lp2lc.Active.DTLC
open Lp2lc.Active.DTLC.Symbolic

namespace Val

def idFn : Val String :=
  .fn fun x => .ref x

end Val

end Sanity
