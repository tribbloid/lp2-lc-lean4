import «Lp2lc».Active.STLC.Serial.Infer

namespace Lp2lc.Active.STLC.AST

open Lp2lc.Active.Util

variable {n : Nat}

namespace Monotone

/-- Every completed inference result, including rejection, is preserved when fuel increases. -/
theorem termInfer (trm : Trm n)
    (bindings : CompilerBindings) :
    (infer trm bindings).Monotone := by
  intro less more result hFuel hInfer
  induction less generalizing n trm bindings more result with
  | zero => simp [infer] at hInfer
  | succ fuel ih =>
    cases more <;> try (exact False.elim (Nat.not_succ_le_zero _ hFuel))
    replace hFuel := Nat.le_of_succ_le_succ hFuel
    cases trm <;> try cases ‹Pure n› <;> try cases ‹Val n›
    all_goals
      simp only [infer.eq_2, infer.eq_3, infer.eq_4, infer.eq_5, infer.eq_6,
        Rec.Outcome.map] at hInfer ⊢
      repeat split at hInfer
      all_goals simp_all

end Monotone

end Lp2lc.Active.STLC.AST
