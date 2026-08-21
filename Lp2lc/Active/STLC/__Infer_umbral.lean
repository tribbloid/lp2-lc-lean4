import «Lp2lc».Active.STLC.__Infer

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

namespace Umbral

structure TypeWithSafey [build : BuildEnv] [env : CompatExeEnv build]
    (trm : AST.Trm env.ExeParameters) where
  t2 : AST.Typ build.BuildParameters
  safety : Safety trm t2


/-
TODO: discharge this function.

In general function should have identical structure with Trm.infer in __Infer.lean, but every output is a `TypeWithSafey`, the safety of the term argument have to be proven on-spot

The original trm2valCtx and trm2typCtx are not designed to hold TypeWithSafey, you will need to make some new context for that
-/
/-- Infers build types for executable terms. -/
def infer [build : BuildEnv] [env : CompatExeEnv build]
    (trm : AST.Trm env.ExeParameters) : RecOpt (TypeWithSafey trm) := sorry

end Umbral

end Lp2lc.Active.STLC
