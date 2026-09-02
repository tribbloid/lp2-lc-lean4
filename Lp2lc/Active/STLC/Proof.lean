import «Lp2lc».Active.STLC.STLCDef
import «Lp2lc».Active.STLC.__Infer
import «Lp2lc».Active.STLC.__Infer_umbral

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util
open Lp2lc.Active.Util.Rec

namespace AST

/-- Evaluation that succeeds with smaller fuel succeeds with the same value at larger fuel. -/
theorem termEvalMonotone [refs : TypOrValRefs] [env : ExeEnv refs]
    (trm : Trm refs.Parameters) :
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
                    cases hBody : (body (env.uid2valCtx.inv input)).eval fuel with
                    | outOfFuel =>
                      simp [AST.eval, hFn, hArg, hBody] at hEval
                    | yield bodyResult =>
                      have hBodyTop := ih fuel (Nat.lt_succ_self fuel)
                        (body (env.uid2valCtx.inv input))
                        toFuel bodyResult hFuelTail hBody
                      simpa [AST.eval, hFn, hArg, hFnTop, hArgTop,
                        hBody, hBodyTop] using hEval
        | ref receipt =>
          cases hRef : refs.uid2either.get receipt with
          | inl value => simpa [AST.eval, hRef] using hEval
          | inr typ => simpa [AST.eval, hRef] using hEval

/-- Inference that succeeds with smaller fuel succeeds with the same type at larger fuel. -/
theorem termInferMonotone [refs : TypOrValRefs] [env : BuildEnv refs]
    (trm : Trm refs.Parameters) :
    trm.infer.Monotone := by
  intro less more result hFuel hInfer
  induction less using Nat.strongRecOn generalizing trm more result with
  | ind fromFuel ih =>
    cases fromFuel with
    | zero =>
      cases trm <;> simp [infer] at hInfer
    | succ fuel =>
      cases more with
      | zero => cases hFuel
      | succ toFuel =>
        have hFuelTail : fuel ≤ toFuel := Nat.le_of_succ_le_succ hFuel
        cases trm with
        | val value =>
          cases value with
          | lit repr => simpa [infer] using hInfer
          | lam body tIn =>
            simp only [infer, Outcome.map] at hInfer ⊢
            split at hInfer
            next _ bodyResult hBody =>
              have hBodyTop := ih fuel (Nat.lt_succ_self fuel)
                _ toFuel bodyResult hFuelTail hBody
              simpa [hBodyTop] using hInfer
            next _ hBody =>
              cases hInfer
        | apply fnTerm arg =>
          cases hFn : fnTerm.infer fuel with
          | outOfFuel => simp [infer, hFn] at hInfer
          | yield fnResult =>
            cases hArg : arg.infer fuel with
            | outOfFuel => simp [infer, hFn, hArg] at hInfer
            | yield argResult =>
              have hFnTop := ih fuel (Nat.lt_succ_self fuel)
                fnTerm toFuel fnResult hFuelTail hFn
              have hArgTop := ih fuel (Nat.lt_succ_self fuel)
                arg toFuel argResult hFuelTail hArg
              simpa [infer, hFn, hArg, hFnTop, hArgTop] using hInfer
        | ref receipt =>
          cases hRef : refs.uid2either.get receipt with
          | inl value =>
            have hValue : value.asTrm.infer fuel = .yield result := by
              simpa [infer, hRef] using hInfer
            have hValueTop := ih fuel (Nat.lt_succ_self fuel)
              value.asTrm toFuel result hFuelTail hValue
            simpa [infer, hRef] using hValueTop
          | inr typ => simpa [infer, hRef] using hInfer

/-- Value inference monotonicity follows from term inference monotonicity. -/
theorem valueInferMonotone [refs : TypOrValRefs] [env : BuildEnv refs]
    (value : Val refs.Parameters) :
    value.asTrm.infer.Monotone :=
  termInferMonotone value.asTrm

end AST

end Lp2lc.Active.STLC
