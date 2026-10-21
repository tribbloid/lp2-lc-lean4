import «Lp2lc».Active.STLC.UId.__Infer

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util Root Root.Trm

section variable {refs : UIdRefs} [build : BuildEnv refs]

/-- Evaluation cannot reject; every returned value can be inferred at the claimed type. -/
def safety (trm : refs.base.Trm) (typ : refs.base.Typ) : Prop :=
  trm.eval.isSemiDecidable
    (λ value => value.asTrm.infer.isDecidable (λ inferred => inferred = typ))

end

namespace Fundamental

section variable {refs : UIdRefs} [build : BuildEnv refs]

/-- Successful runtime inference excludes evaluation rejection and preserves the result's type. -/
theorem main (trm : refs.base.Trm) (fuel : Nat) (typ : refs.base.Typ)
    (hInfer : trm.infer fuel = .yield (some typ)) : safety trm typ := sorry

end

end Fundamental

end Lp2lc.Active.STLC
