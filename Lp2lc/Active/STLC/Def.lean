import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.LC.Def
import «Lp2lc».Util

namespace Lp2lc.Active

namespace STLC

inductive AST(F: Rep) : Rep
| backbone : {w : Which} -> LC.AST F w -> AST F w
| fnT: (I: F .typ) -> (O: F .typ) -> AST F .typ -- {x => out(x)} : I => O

infixr:60 " ==> " => AST.fnT

end STLC

end Lp2lc.Active
