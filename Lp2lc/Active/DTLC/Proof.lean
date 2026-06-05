import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util
import «Lp2lc».Active.DTLC.DTLCDef

namespace Lp2lc.Active

namespace DTLC

open AST
open Lp2lc.Active.Util

theorem AdequacyLemma {impl : Impl}
    [Compiler.Env impl] [Runtime.Env impl]
    (src : Trm impl) (fuel : Nat) :
    src.IsAdequate fuel := sorry


end DTLC

end Lp2lc.Active
