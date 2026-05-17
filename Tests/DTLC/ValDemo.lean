import «Lp2lc».Active.DTLC.Def

namespace Tests.DTLC.Sanity
open Lp2lc.Active.DTLC

namespace Val

def idFn : ValAST :=
  .fn (body := fun x => .ref x)

end Val

end Sanity
