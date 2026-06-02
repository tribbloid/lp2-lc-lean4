import «Lp2lc».Active.DTLC.DTLCDef

namespace Lp2lc.Active

namespace DTLC

open Lp2lc.Active.Util

inductive Symbol where -- no constructor, it can only be retrieved from FBound

namespace Symbolic

abbrev Typ (ByteCode : Type) := AST.Typ Symbol ByteCode
abbrev Val (ByteCode : Type) := AST.Val Symbol ByteCode
abbrev Trm (ByteCode : Type) := AST.Trm Symbol ByteCode

end Symbolic

end DTLC

end Lp2lc.Active
