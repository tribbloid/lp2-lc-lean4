import «Lp2lc».Active.STLC.Serial.__Eval_certifiedByInfer
import «Lp2lc».Active.STLC.Serial.Eval

namespace Lp2lc.Active.STLC.AST.CertifiedByInferAudit

open Lp2lc.Active.Util

/-- Erasing the certificate preserves ordinary evaluation after successful inference. -/
theorem agreement {n} (trm : Trm n) (bindings : ExeBindings) (fuel inferFuel : Nat)
    (typ : Typ) (hInfer : trm.infer bindings inferFuel = .yield (some typ)) :
    (trm.eval_certified bindings hInfer fuel).map (λ payload => some payload.v) =
      trm.eval bindings fuel := by
  sorry

#print axioms eval_certified
#print axioms agreement

end Lp2lc.Active.STLC.AST.CertifiedByInferAudit
