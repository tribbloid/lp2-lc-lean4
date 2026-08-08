import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.STLC.__Infer

namespace Lp2lc.Active

namespace STLC
open Lp2lc.Active.Util

section variable {F : Free}

namespace Umbral

section variable [@ProvingBase F]

structure SafetyOf (trm : AST.Trm F) where
  typ : AST.Typ F
  -- safety : Safety trm typ -- TODO: this lemma has been temporarily disabled. Enable it later.

abbrev Compilation (trm : AST.Trm F) :=
  RecOption (SafetyOf trm) -- namely, the semi-decidability of executing term

/-- Requires the proving computation to shadow every outcome of term inference. -/
structure Objective (trm : AST.Trm F) : Type where
  compilation : Compilation trm
  sameInfer : ∀ (fuel : Nat),
    (compilation fuel).map (Option.map SafetyOf.typ) = trm.infer fuel

end

/--
contains a FBound store to save/load intermediate safety proof for both `AST.Trm` and `AST.Val`

`infer_prove` & any theorem that relies on safety can use it, this is the only correspondence between compiletime and runtime variables.
-/
class ProvingEnv extends @ProvingBase F where


namespace ProvingEnv
-- TODO: add proofCtx here, a new Aux0 should be created. No abstract function is allowed

-- all declarations of Fixpoint and it's dependently typed instance should be in this namespace
end ProvingEnv

section variable [@ProvingEnv F]

/--
like `Trm.infer` it inductively infer `Typ` of a given `Trm`, using the structure of `Trm.infer` as a blueprint.

unlike `Trm.infer` it is obliged to produce a [Objective] bundle of:

- original `Typ`
- proof that it has the same result to `Trm.infer`
- proof that the `Trm : Typ` pair is safe to evaluate
-/
def infer_prove [env: @ProvingEnv F] (trm : AST.Trm F) : Objective trm :=
  sorry

end

end Umbral
end

end STLC
