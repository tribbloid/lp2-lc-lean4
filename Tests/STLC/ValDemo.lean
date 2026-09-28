import «Lp2lc».Active.STLC.STLCDef

namespace Tests.STLC.Sanity

open Lp2lc.Active.STLC

namespace Symbolic

abbrev Typ := AST.Typ (AST.At 0)
abbrev Val := AST.Val (AST.At 0)
abbrev Trm := AST.Trm (AST.At 0)

end Symbolic

open Symbolic

namespace Val

def idFn : Val :=
  .fn .TLit (.mk (λ proxy => .ref proxy))

end Val

end Tests.STLC.Sanity
