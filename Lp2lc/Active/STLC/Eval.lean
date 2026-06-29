
import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util
import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active

namespace STLC
open Lp2lc.Active.Util

/-
this file proof an alternative theorem for STLC soundness:

term can be inferred to type using some fuel, evaluating it must leads to either a variable that can be inferred to a lesser type with some (less?) fuel or loop.

Obviously inferring type is not alway available in more complex type system, but it's a good demo for recursive proving
-/

section variable {I : Free}

namespace AST.Trm

/-- Inference that succeeds with smaller fuel succeeds with the same type at larger fuel. -/
theorem termEvalMonotone [env : @RuntimeEnv I]
    (trm : Trm I) :
    let self := trm.eval
    self.Monotone := by sorry

end Trm
end
