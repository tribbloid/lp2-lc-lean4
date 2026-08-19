import «Lp2lc».Active.STLC.__Infer

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

namespace Umbral

/-- Combines the executable and build-time environments, equating their value bridges. -/
class UmbralEnv extends ProvingBase where

namespace UmbralEnv

end UmbralEnv

structure TypeWithSafey [env : ProvingBase] (trm : AST.Trm env.ExeParameters) where
  t2 : AST.Typ env.BuildParameters
  safety : Safety trm t2


/-- Infers build types for executable terms. -/
def infer [env : UmbralEnv]
    (trm : AST.Trm env.ExeParameters) : RecOpt (TypeWithSafey trm) := sorry

end Umbral

end Lp2lc.Active.STLC
