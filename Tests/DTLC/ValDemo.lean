import «Lp2lc».Active.DTLC.Impl

namespace Tests.DTLC.Sanity
open Lp2lc.Active.DTLC
open Lp2lc.Active.DTLC.Symbolic

namespace Val

def idFn : Val :=
  .fn fun x => .ref x

end Val

end Sanity
