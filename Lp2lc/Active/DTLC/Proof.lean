import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util
import «Lp2lc».Active.DTLC.Def

namespace Lp2lc.Active

namespace DTLC

open AST
open Util

theorem AdequacyLemma {I : Index} [Compiletime.Env I] [Runtime.Env I]
    (src : Trm I) (fuel : Nat) :
    src.IsAdequate fuel := sorry


end DTLC

end Lp2lc.Active
