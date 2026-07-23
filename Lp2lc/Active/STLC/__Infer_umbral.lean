import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.STLC.__Infer

namespace Lp2lc.Active

namespace STLC
open Lp2lc.Active.Util

section variable {F : Free}

namespace Umbral

section variable [@ProvingBase F]

structure InferenceWProof (trm: AST.Trm F) : Type where
  typ: AST.Typ F
  sameInfer: trm.infer.isDecidable (λ t2 => typ <= t2)
  safetyProof: Safety trm typ

end

/--
primary key structure to link/associate a CompilerEnv.typeCtx entry and a RuntimeEnv.valueCtx entry

there is no guarantee that typeUID & valueUID will be identical, so this is the only evidence that they are related
-/
-- structure UIDLink where
--   typeUID: F.Index
--   valueUID: F.Index

class ProvingEnv where
  base: @ProvingBase F
  proofGroup : FBoundGroup F.Index (AST.Trm F)
  proofCtx : FBoundV2 proofGroup (@InferenceWProof F base) -- TODO: need a concrete value type to save proof

instance [env: @ProvingEnv F] : @ProvingBase F := env.base

section variable [@ProvingEnv F]

/--
similar to Trm.infer, even have similar structure

but instead of producing only a Typ F, it is obliged to produce all the following elements:
- Typ F
- proof that it is equal to the result of Trm.infer
- proof that it is safe after evaluation
-/
def infer_umbral [env: @ProvingEnv F] (trm : AST.Trm F) : RecOption (@InferenceWProof F env.base trm) :=
  sorry

-- theorem termInferMonotone [env : @ProvingEnv F]
--     (trm : AST.Trm F) :
--      (infer trm).Monotone := sorry

end

end Umbral
end

end STLC
