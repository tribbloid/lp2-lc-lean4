import Batteries.Tactic.OpenPrivate

import «Lp2lc».Active.DSub.Serial.__Eval_certifiedByInfer

namespace Lp2lc.Active.DSub.AST.CertifiedByInfer

open Lp2lc.Active.Util

-- Evaluation properties reuse the certified evaluator and its private monotonicity support.
open private evalInternal AST.Monotone.termInfer CompilerTyp.Monotone.subtype
  from Lp2lc.Active.DSub.Serial.__Eval_certifiedByInfer

namespace Monotone

/-- Completed evaluation results are preserved when fuel increases. -/
theorem termEval {n} (trm : Trm n) (bindings : ExeBindings) (validationFuel : Nat) :
    (evalInternal trm bindings validationFuel).Monotone := by
  intro less more result hFuel h
  induction less generalizing n trm bindings more result with
  | zero => cases h
  | succ fuel ih =>
    cases more with
    | zero => exact False.elim (Nat.not_succ_le_zero _ hFuel)
    | succ more =>
      replace hFuel := Nat.le_of_succ_le_succ hFuel
      have hRun {m} (self : Trm m) entries value :
          (evalInternal self entries validationFuel fuel).map (·.map Subtype.val) = .yield value →
          (evalInternal self entries validationFuel more).map (·.map Subtype.val) = .yield value := by
        cases hResult : evalInternal self entries validationFuel fuel with
        | outOfFuel => simp [Rec.Outcome.map]
        | yield result =>
          intro h
          rw [ih self entries more result hFuel hResult]
          exact h
      have hValidation : max validationFuel (fuel + 1) ≤ max validationFuel (more + 1) := by omega
      have hInfer := @AST.Monotone.termInfer
      have hSubtype := CompilerTyp.Monotone.subtype
      simp only [Rec.Monotone] at hInfer hSubtype
      cases trm <;> try cases ‹Pure n›
      all_goals simp only [evalInternal, Rec.Outcome.flatMap] at h ⊢
      all_goals repeat' split at h
      all_goals try grind (splits := 0)
      all_goals
        first
        | rename_i hRaw expected actual hSource hValue hSubtypeCheck
          split at hRaw
        | rename_i hRaw
          split at hRaw
      all_goals repeat' split at hRaw
      all_goals grind (splits := 1)

end Monotone

end Lp2lc.Active.DSub.AST.CertifiedByInfer
