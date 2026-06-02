import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util
import «Lp2lc».Active.DTLC.Def

namespace Lp2lc.Active

namespace DTLC

open AST
open Util

theorem AdequacyLemma {I : Index} {ByteCode : Type}
    [Compiletime.Env I ByteCode] [Runtime.Env I ByteCode]
    (src : Trm I ByteCode) (fuel : Nat) :
    src.IsAdequate fuel := sorry


end DTLC

end Lp2lc.Active
