import «Lp2lc».Active.DTLC.Def

namespace Tests.DTLC.Sanity
open Lp2lc.Active.DTLC
open Lp2lc.Active.DTLC.Closed

namespace Val

def idFn : ValAST :=
  .fn fun x => .ref x

end Val

end Sanity
