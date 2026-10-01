import «Lp2lc».Active.STLC.STLCDef

namespace Tests.STLC.Sanity

open Lp2lc.Active.STLC
open Lp2lc.Active.Util

namespace Val

def idFn : AST 0 .val :=
  .fn .TLit (.mk (λ proxy => .ref proxy))

end Val

end Tests.STLC.Sanity
