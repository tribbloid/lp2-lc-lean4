import Mathlib.Tactic

import «Lp2lc».Active.Shared
import «Lp2lc».Active.STLC.Def

namespace Lp2lc.Active

namespace SysF

inductive AST(F: Rep) : Rep
| backbone : {w : Which} -> STLC.AST F w -> AST F w
| polyFn : (I: F .typ) -> (out: F .trm) -> AST F .trm -- polymorphic function {[I] => out}, out may contain I
| polyApp : (poly: F .trm) -> (X: F .typ) -> AST F .trm -- apply polymorphic function {poly[X]}
| bvarT : Nat -> AST F .typ -- like bvar, but for type
| fvarT : Var -> AST F .typ -- like fvar, but for type

end SysF

end Lp2lc.Active
