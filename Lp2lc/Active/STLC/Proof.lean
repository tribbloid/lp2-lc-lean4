import «Lp2lc».Active.STLC.STLCDef
import «Lp2lc».Active.STLC.__Infer

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util
open Lp2lc.Active.Util.Rec

namespace AST

/-- Evaluation that succeeds with smaller fuel succeeds with the same value at larger fuel. -/
theorem termEvalMonotone [refs : ExeRefs] [env : ExeEnv refs]
    (trm : Trm refs.ExeParameters) :
    trm.eval.Monotone := by
  intro less more result hFuel hEval
  induction less using Nat.strongRecOn generalizing trm more result with
  | ind fromFuel ih =>
    cases fromFuel with
    | zero =>
      cases trm <;> simp [AST.eval] at hEval
    | succ fuel =>
      cases more with
      | zero => cases hFuel
      | succ toFuel =>
        have hFuelTail : fuel ≤ toFuel := Nat.le_of_succ_le_succ hFuel
        cases trm with
        | val value =>
          simpa [AST.eval] using hEval
        | apply fnTerm arg =>
          cases hFn : fnTerm.eval fuel with
          | outOfFuel => simp [AST.eval, hFn] at hEval
          | yield fnResult =>
            have hFnTop := ih fuel (Nat.lt_succ_self fuel)
              fnTerm toFuel fnResult hFuelTail hFn
            cases hArg : arg.eval fuel with
            | outOfFuel => simp [AST.eval, hFn, hArg] at hEval
            | yield argResult =>
              have hArgTop := ih fuel (Nat.lt_succ_self fuel)
                arg toFuel argResult hFuelTail hArg
              cases fnResult with
              | none =>
                simpa [AST.eval, hFn, hArg, hFnTop, hArgTop] using hEval
              | some fnValue =>
                cases fnValue with
                | lit repr =>
                  simpa [AST.eval, hFn, hArg, hFnTop, hArgTop] using hEval
                | lam body tIn =>
                  cases argResult with
                  | none =>
                    simpa [AST.eval, hFn, hArg, hFnTop, hArgTop] using hEval
                  | some input =>
                    cases hBody :
                        (body.specialise (Parameters.CarrierMap.identity _)
                          (.inr (env.uid2valCtx.inv input))).eval fuel with
                    | outOfFuel =>
                      simp only [AST.eval, hFn, hArg, hBody] at hEval
                      cases hEval
                    | yield bodyResult =>
                      have hBodyTop := ih fuel (Nat.lt_succ_self fuel)
                        (body.specialise (Parameters.CarrierMap.identity _)
                          (.inr (env.uid2valCtx.inv input)))
                        toFuel bodyResult hFuelTail hBody
                      simpa only [AST.eval, hFn, hArg, hFnTop, hArgTop,
                        hBody, hBodyTop] using hEval
        | ref receipt =>
          cases receipt with
          | inl rc =>
            simpa [AST.eval] using hEval
          | inr rc =>
            simpa [AST.eval] using hEval


end AST

end Lp2lc.Active.STLC
