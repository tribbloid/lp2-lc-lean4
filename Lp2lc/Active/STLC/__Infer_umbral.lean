import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.STLC.__Infer

namespace Lp2lc.Active

namespace STLC
open Lp2lc.Active.Util

section variable {F : Free}

namespace Umbral

section variable [@ProvingBase F]

abbrev ProvenCondition (trm2typ: AST.Trm2Typ F) : Prop :=
  Safety trm2typ.trm trm2typ.typ -- TODO: should this objective be delayed?

abbrev ProvingResult (trm : AST.Trm F) :=
  RecOption (PSigma (λ typ : AST.Typ F => ProvenCondition ⟨trm, typ⟩))

/-- Requires the proving computation to shadow every outcome of term inference. -/
structure Objective (trm : AST.Trm F) : Type where
  proving : ProvingResult trm
  sameInfer : ∀ (fuel : Nat),
    (proving fuel).map (Option.map PSigma.fst) = trm.infer fuel

end


/--
contains a FBound store to save/load intermediate safety proof for both `AST.Trm` and `AST.Val`

`infer_prove` & any theorem that relies on safety can use it, this is the only correspondence between compiletime and runtime variables.
-/
class ProvingEnv extends @ProvingBase F where


namespace ProvingEnv
-- TODO: add proofCtx here, a new Aux0 should be created. No abstract function is allowed
end ProvingEnv

section variable [@ProvingEnv F]

/--
like `Trm.infer` it inductively infer `Typ` of a given `Trm`, using the structure of `Trm.infer` as a blueprint.

unlike `Trm.infer` it is obliged to produce a `ProvenCondition` bundle of:

- original `Typ`
- proof that it has the same result to `Trm.infer`
- proof that the `Trm : Typ` pair is safe to evaluate
-/
def infer_prove [env: @ProvingEnv F] (trm : AST.Trm F) : Objective trm :=
  sorry

-- theorem termInferMonotone [env : @ProvingEnv F]
--     (trm : AST.Trm F) :
--      (infer trm).Monotone := sorry


end

end Umbral
end

end STLC
