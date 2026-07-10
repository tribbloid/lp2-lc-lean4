import Std
import «Lp2lc».Active.STLC_CE.STLCDef

namespace Lp2lc.Active

namespace STLC_CE

open Lp2lc.Active.Util

namespace AST.Trm

/-- Evaluation that succeeds with smaller fuel succeeds with the same value at larger fuel. -/
theorem termEvalMonotone {ctx : AST.Ctx}
    (env : AST.RuntimeEnv ctx) (trm : AST.Trm ctx) :
    (trm.eval env).Monotone := by
  intro less more result hFuel hEval
  induction less using Nat.strongRecOn generalizing ctx env trm more result with
  | ind fromFuel ih =>
    cases fromFuel with
    | zero =>
      cases trm <;> simp [AST.Trm.eval] at hEval
    | succ fuel =>
      cases more with
      | zero => cases hFuel
      | succ toFuel =>
        have hFuelTail : fuel <= toFuel := Nat.le_of_succ_le_succ hFuel
        cases trm with
        | val value =>
          cases value <;> simpa [AST.Trm.eval] using hEval
        | apply fnTerm arg =>
          cases hFn : AST.Trm.eval fnTerm env fuel with
          | outOfFuel => simp [AST.Trm.eval, hFn] at hEval
          | yield fnResult =>
            have hFnTop := ih fuel (Nat.lt_succ_self fuel) env fnTerm toFuel fnResult hFuelTail hFn
            cases hArg : AST.Trm.eval arg env fuel with
            | outOfFuel => simp [AST.Trm.eval, hFn, hArg] at hEval
            | yield argResult =>
              have hArgTop := ih fuel (Nat.lt_succ_self fuel) env arg toFuel argResult hFuelTail hArg
              cases fnResult with
              | none =>
                simpa [AST.Trm.eval, hFn, hArg, hFnTop, hArgTop] using hEval
              | some fnValue =>
                rcases fnValue with ⟨_, savedEnv, fnValue⟩
                cases fnValue with
                | primitive repr =>
                  simpa [AST.Trm.eval, hFn, hArg, hFnTop, hArgTop] using hEval
                | fn tIn body =>
                  cases argResult with
                  | none =>
                    simpa [AST.Trm.eval, hFn, hArg, hFnTop, hArgTop] using hEval
                  | some input =>
                    rcases input with ⟨_, inputEnv, inputValue⟩
                    cases hBody : AST.Trm.eval (body .ptop) (savedEnv.snoc inputEnv inputValue) fuel with
                    | outOfFuel =>
                      simp [AST.Trm.eval, hFn, hArg, hBody] at hEval
                    | yield bodyResult =>
                      have hBodyTop :=
                        ih fuel (Nat.lt_succ_self fuel)
                          (savedEnv.snoc inputEnv inputValue) (body .ptop) toFuel bodyResult
                          hFuelTail hBody
                      simpa [AST.Trm.eval, hFn, hArg, hFnTop, hArgTop, hBody, hBodyTop] using hEval
        | ref top =>
          simpa [AST.Trm.eval] using hEval

end AST.Trm

end STLC_CE

end Lp2lc.Active
