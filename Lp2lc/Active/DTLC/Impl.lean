import «Lp2lc».Active.DTLC.DTLCDef

namespace Lp2lc.Active

namespace DTLC

open Lp2lc.Active.Util

inductive Symbol where -- no constructor, it can only be retrieved from FBound

namespace Symbolic

abbrev ByteCode := String
abbrev Typ := AST.Typ Symbol ByteCode
abbrev Val := AST.Val Symbol ByteCode
abbrev Trm := AST.Trm Symbol ByteCode

end Symbolic

end DTLC

end Lp2lc.Active
