import «Lp2lc».Active.STLC.Serial.Auxiliary
import «Lp2lc».Active.STLC.Serial.Eval
import «Lp2lc».Active.STLC.UId.Eval

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

namespace AST

namespace Monotone

/-- Evaluation that succeeds with smaller fuel succeeds with the same value at larger fuel. -/
theorem termEval {n} (trm) (bindings : ExeBindings) :
    (eval (n := n) trm bindings).Monotone := by
  intro less more result hFuel hEval
  induction less generalizing n trm bindings more result with
  | zero => simp [eval] at hEval
  | succ fuel ih =>
    cases more <;> try (exact False.elim (Nat.not_succ_le_zero _ hFuel))
    replace hFuel := Nat.le_of_succ_le_succ hFuel
    cases trm <;> (try cases ‹Pure n›) <;> simp only [eval.eq_2, eval.eq_3, eval.eq_4] at hEval ⊢
    all_goals
      repeat split at hEval
      all_goals simp_all
      all_goals
        first
        | rename_i context tIn body captured value hFn hArg
          cases hCheck : infer value.value.asTrm value.captured fuel with
          | outOfFuel => simp [hCheck, Rec.Outcome.flatMap] at hEval
          | yield typ =>
            have hMore := termInfer _ _ _ _ _ hFuel hCheck
            simp only [hCheck, hMore, Rec.Outcome.flatMap] at hEval ⊢
            split at hEval <;> simp_all
        | rename_i context tOut op captured argContext repr argCaptured hFn hArg
          cases hCheck : infer (.pure (.val (op repr))) captured fuel with
          | outOfFuel => simp [hCheck, Rec.Outcome.map] at hEval
          | yield typ =>
            have hMore := termInfer _ _ _ _ _ hFuel hCheck
            simpa only [hCheck, hMore] using hEval
        | subst_vars; cases ‹Return ExeVal› <;>
            (try cases ‹ExeVal›) <;> (try cases ‹Val _›) <;> rfl

end Monotone

end AST

namespace Root.Trm

namespace Monotone

variable {refs : UIdRefs} [build : BuildEnv refs]

/-- Runtime inference preserves every completed result when fuel increases. -/
theorem termInfer (trm : refs.base.Trm) : trm.infer.Monotone := by
  intro less more result le h
  induction less generalizing trm more result with
  | zero => simp [infer] at h
  | succ less ih =>
    cases more <;> try omega
    have le := Nat.le_of_succ_le_succ le
    cases trm <;> try cases ‹Pre.AST _ .pure› <;> try cases ‹Pre.AST _ .val›
    all_goals
      simp only [infer.eq_2, infer.eq_3, infer.eq_4, infer.eq_5, infer.eq_6, Rec.Outcome.map] at h ⊢
      repeat split at h
      all_goals simp_all

/-- Evaluation preserves every completed result, including rejection, when fuel increases. -/
theorem termEval (trm : refs.base.Trm) :
    trm.eval.Monotone := by
  intro less more result hFuel hEval
  induction less generalizing trm more result with
  | zero => simp [eval] at hEval
  | succ fuel ih =>
    cases more <;> try omega
    replace hFuel := Nat.le_of_succ_le_succ hFuel
    cases trm <;> (try cases ‹Pre.AST _ .pure›) <;> simp only [eval.eq_2, eval.eq_3, eval.eq_4] at hEval ⊢
    all_goals
      repeat split at hEval
      all_goals simp_all
      all_goals
        first
        | rename_i tOut op repr hFn hArg
          cases hCheck : infer (.pure (.val (op repr))) fuel with
          | outOfFuel => simp [hCheck, Rec.Outcome.map] at hEval
          | yield typ =>
            have hMore := termInfer _ _ _ _ hFuel hCheck
            simpa only [hCheck, hMore] using hEval
        | subst_vars; cases ‹Return refs.base.Val› <;> (try cases ‹refs.base.Val›) <;> rfl

end Monotone

end Root.Trm

end Lp2lc.Active.STLC
