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
-/
structure UIDBundle where
  typeUID: F.Index
  valueUID: F.Index

class ProvingEnv extends (@RuntimeEnv F), (@CompilerEnv F) where

def inferShadow [env: @CompilerEnv I] (self : AST.Trm I) : RecOption (AST.Typ I) := -- TODO: return Typ with safety proof
  sorry

end ShadowProof
end

end STLC
