import «Lp2lc».Active.STLC.Serial.__Eval_certifiedByInfer

namespace Lp2lc.Active.STLC.AST.CertifiedByInferAudit

open Lp2lc.Active.Util

/-- Erasing the certificate preserves ordinary evaluation for every term and fuel. -/
theorem agreement {n} (trm : Trm n) (bindings : ExeBindings) (fuel : Nat) :
    (trm.eval_certified bindings).result fuel = trm.eval bindings fuel := by
  induction fuel generalizing n trm bindings with
  | zero => rfl
  | succ fuel ih =>
    cases trm with
    | val value => rfl
    | ref carrier under => rfl
    | apply fn arg =>
      change (match (AST.eval_certified fn bindings).result fuel, (AST.eval_certified arg bindings).result fuel with
        | .yield (some (.mk context (.fn _ body) captured)), .yield (some value) =>
          (AST.eval_certified (body.apply .only) (captured.set (context + 1) value)).result fuel
        | .yield _, .yield _ => .yield none
        | _, _ => .outOfFuel) = _
      rw [eval.eq_4, ih, ih]
      cases AST.eval fn bindings fuel with
      | outOfFuel => cases AST.eval arg bindings fuel <;> rfl
      | yield candidate =>
        cases candidate with
        | none => cases AST.eval arg bindings fuel <;> rfl
        | some fnValue =>
          cases fnValue with
          | mk context fnValue captured =>
            cases fnValue with
            | lit repr => cases AST.eval arg bindings fuel <;> rfl
            | fn annotation body =>
              cases AST.eval arg bindings fuel with
              | outOfFuel => rfl
              | yield candidate =>
                cases candidate with
                | none => rfl
                | some value => exact ih (body.apply .only) (captured.set (context + 1) value)

#print axioms eval_certified
#print axioms agreement

end Lp2lc.Active.STLC.AST.CertifiedByInferAudit
