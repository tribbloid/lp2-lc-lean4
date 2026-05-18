import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Util

namespace Lp2lc.Active

namespace STLC

/-- Shared STLC syntax family, currently exposing function types over the common representation. -/
inductive AST (F : Rep) : Rep
| fnT (I : F .typ) (O : F .typ) : AST F .typ -- {x => out(x)} : I => O

infixr:60 " ==> " => AST.fnT

end STLC

end Lp2lc.Active
