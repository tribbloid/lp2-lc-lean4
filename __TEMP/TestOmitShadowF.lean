import «Lp2lc».Active.STLC.__Infer

namespace Lp2lc.Active.STLC.TestOmitShadowF

open Lp2lc.Active.Util

section


variable {F : Free}

structure InferenceWProof (F : Free) [@ProvingBase F] where
  trm : AST.Trm F
  typ : AST.Typ F
  sameInfer : trm.infer.isDecidable (λ t => t <= typ)
  safetyProof : Safety trm typ

structure UIDLink (F : Free) where
  typeUID : F.Index
  valueUID : F.Index

class ShadowProvingEnv where
  base : @ProvingBase F
  proofCtx : UIDEquiv (UIDLink F) (@InferenceWProof F base)

instance [env : @ShadowProvingEnv F] : @ProvingBase F := env.base

section

variable [@ShadowProvingEnv F]

def inferRigorously [env : @CompilerEnv F]
    (self : AST.Trm F) : RecOpt (InferenceWProof F) :=
  sorry

end


end


end Lp2lc.Active.STLC.TestOmitShadowF
