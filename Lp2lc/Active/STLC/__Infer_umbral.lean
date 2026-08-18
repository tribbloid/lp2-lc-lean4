import «Lp2lc».Active.STLC.__Infer

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

/-- Adds the compile-time typing context to an execution environment. -/
class UmbralEnv extends ExeEnv

namespace UmbralEnv
section variable (env : UmbralEnv)

def trm2proofCtx :=
  env.mkFixpoint (λ T =>
    let TC := env.trm2valCtx.UId ⊕ T
    AST.Val { C := TC, D := env.D })

abbrev UmbralParameters : Parameters :=
  { C := env.trm2valCtx.UId ⊕ env.trm2proofCtx.UId, D := env.D }

end
end UmbralEnv

namespace Umbral



-- /-- Infers build types for executable terms. -/
-- def infer [env : UmbralEnv]
--     (self : Trm env.ExeParameters) : RecOpt (Typ env.UmbralParameters) :=


end Umbral

end Lp2lc.Active.STLC
