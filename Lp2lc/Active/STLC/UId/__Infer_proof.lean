import «Lp2lc».Active.STLC.UId.__Infer

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util EnvBase EnvBase.Trm

section variable {refs : UIdRefs} [build : BuildEnv refs] [exe : ExeEnv refs]

/-- Every completed evaluation succeeds, and its value can be inferred at the claimed type. -/
def Safety (trm : refs.base.Trm) (typ : refs.base.Typ) : Prop :=
  trm.eval.isSemiDecidable
    (λ value => value.asTrm.infer.isDecidable (λ inferred => inferred ≤ typ))

/-- Successful runtime inference excludes evaluation rejection and preserves the result's type. -/
theorem fundamental (trm : refs.base.Trm) (fuel : Nat) (typ : refs.base.Typ)
    (hInfer : trm.infer fuel = .yield (some typ)) : Safety trm typ := by
  sorry

end
end Lp2lc.Active.STLC
