import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.STLC.__Infer

namespace Lp2lc.Active

namespace STLC
open Lp2lc.Active.Util

section variable {F : Free}

namespace Umbral

section variable [@ProvingBase F]

structure InferenceWProof (trm2typ: AST.Trm2Typ F) : Type where
  sameInfer: trm2typ.trm.infer.isDecidable (λ t2 => trm2typ.typ <= t2)
  safetyProof: Safety trm2typ.trm trm2typ.typ

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
  proofCtx : base.trm2typCtx.Aux (λ t => @InferenceWProof F base t) -- TODO: need a concrete value type to save proof

instance [env: @ProvingEnv F] : @ProvingBase F := env.base

section variable [@ProvingEnv F]

/--
similar to Trm.infer, even have similar structure

but instead of producing only a Typ F, it is obliged to produce all the following elements:
- Typ F
- proof that it is equal to the result of Trm.infer
- proof that it is safe after evaluation
-/
def infer_umbral [env: @ProvingEnv F] (trm : AST.Trm F) :
    RecOption (PSigma (λ typ : AST.Typ F => @InferenceWProof F env.base ⟨trm, typ⟩)) :=
  sorry

-- theorem termInferMonotone [env : @ProvingEnv F]
--     (trm : AST.Trm F) :
--      (infer trm).Monotone := sorry

end

end Umbral
end

end STLC
