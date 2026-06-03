import «Lp2lc».Active.DTLC.DTLCDef

namespace Lp2lc.Active

namespace DTLC

open Lp2lc.Active.Util

inductive Symbol where -- no constructor, it can only be retrieved from FBound

namespace Symbolic

@[reducible] def impl : Impl where
  I := Symbol
  ByteCode := String

abbrev ByteCode := impl.ByteCode
abbrev Typ := AST.Typ impl
abbrev Val := AST.Val impl
abbrev Trm := AST.Trm impl

end Symbolic

end DTLC

end Lp2lc.Active
