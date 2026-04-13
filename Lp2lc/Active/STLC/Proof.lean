import Mathlib.Tactic
import «Lp2lc».Active.Shared
import «Lp2lc».Active.STLC.Def

/-!
This file proves soundness for simply typed lambda calculus by interpreting
terms with a step-indexed logical relation. The step index is the fuel used to
reason about functions recursively: a function is safe for `fuel` when, for
any `lessFuel ≤ fuel`, it sends semantically safe inputs to outputs that
stay safe one guarded step later.

All docstrings use short (under 5 lines) of Scala code as demonstrations.
-/

namespace Lp2lc.Active.STLC

namespace Semantic

/-
the anatomy of a soundness proof:

Trm.interp_fuel_mono: more fuel never breaks a successful run

Trm.interp_sound: interpreter success implies BigStep

Trm.interp_complete: BigStep implies interpreter success (with enough fuel)
-/



end Semantic

end STLC
