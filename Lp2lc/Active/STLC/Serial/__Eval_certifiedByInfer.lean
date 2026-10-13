import «Lp2lc».Active.STLC.Serial.__Infer

namespace Lp2lc.Active.STLC.AST

open Lp2lc.Active.Util

namespace CertifiedByInfer

/-- An evaluation outcome paired with safety under the existing inference rule.

Successful inference excludes rejection and preserves the type of every returned
value in its captured environment. Evaluation may still exhaust its fuel.
-/
structure Result {n} (trm : Trm n) (bindings : ExeBindings) where
  result : Rec.Outcome (Option ExeValue)
  safe : ∀ inferFuel typ, trm.infer bindings inferFuel = .yield (some typ) →
    match result with
    | .outOfFuel => True
    | .yield none => False
    | .yield (some value) =>
      ∃ valueFuel, value.value.asTrm.infer value.captured valueFuel = .yield (some typ)

end CertifiedByInfer

/-- Evaluate with an erased safety proof constructed at every recursive step.

The result contains both the ordinary outcome and its certificate. No typing
witness is needed to run evaluation; `safe` applies to any successful inference
of the original term, with an independent inference fuel budget.
-/
def eval_certified {n} (self : Trm n) (bindings : ExeBindings := .empty) :
    (fuel : Nat) → CertifiedByInfer.Result self bindings := by
  sorry

end Lp2lc.Active.STLC.AST
