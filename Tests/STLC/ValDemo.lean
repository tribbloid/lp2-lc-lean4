import «Lp2lc».Active.STLC.STLCDef

namespace Tests.STLC.Sanity

open Lp2lc.Active.STLC
open Lp2lc.Active.Util

namespace Symbolic

abbrev Typ := AST.Typ CtxEmbedding.DeBruijn.toParameters
abbrev Val := AST.Val CtxEmbedding.DeBruijn.toParameters
abbrev Trm := AST.Trm CtxEmbedding.DeBruijn.toParameters

end Symbolic

open Symbolic

namespace Val

def idFn : Val :=
  .fn .TLit (.mk (λ proxy => .ref proxy))

end Val

end Tests.STLC.Sanity
