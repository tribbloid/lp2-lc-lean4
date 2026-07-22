import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.STLC.__Infer

namespace Lp2lc.Active

namespace STLC
open Lp2lc.Active.Util

section variable {F : Free}
namespace ShadowProof

/--
primary key structure to link/associate a CompilerEnv.typeCtx entry and a RuntimeEnv.valueCtx entry

there is no other way that can relate both entries: the keys are usually not different
-/
structure UIDLink where
  typeUID: F.Index
  valueUID: F.Index

section variable [@ProvingBase F]

structure RigorousInferredTyp where
  trm: AST.Typ F
  typ: AST.Typ F
  sameEval: trm.eval = typ
  safetyProof: Safety trm typ

end

def inferShadow [env: @CompilerEnv F] (self : AST.Trm F) : RecOption (AST.Typ F) := -- TODO: return Typ with safety proof
  sorry

end ShadowProof
end

end STLC
