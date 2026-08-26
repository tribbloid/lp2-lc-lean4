import «Lp2lc».Active.STLC.STLCDef
import «Lp2lc».Active.STLC.__Infer
import «Lp2lc».Active.STLC.__Infer_umbral

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
                        (body.instantiateLamBody (env.uid2valCtx.inv input)).eval fuel with
                    | outOfFuel =>
                      simp only [AST.eval, hFn, hArg, hBody] at hEval
                      cases hEval
                    | yield bodyResult =>
                      have hBodyTop := ih fuel (Nat.lt_succ_self fuel)
                        (body.instantiateLamBody (env.uid2valCtx.inv input))
                        toFuel bodyResult hFuelTail hBody
                      simpa only [AST.eval, hFn, hArg, hFnTop, hArgTop,
                        hBody, hBodyTop] using hEval
        | ref receipt =>
          cases receipt with
          | inl rc =>
            simpa [AST.eval] using hEval
          | inr rc =>
            simpa [AST.eval] using hEval

/-- Inference that succeeds with smaller fuel succeeds with the same type at larger fuel. -/
theorem termInferMonotone [refs : ExeRefs] [env : BuildEnv refs]
    (trm : Trm env.BuildParameters) : -- TODO: lift this core theorem to `infer`
    trm.inferCore.Monotone := by
  intro less more result hFuel hInfer
  induction less using Nat.strongRecOn generalizing trm more result with
  | ind fromFuel ih =>
    cases fromFuel with
    | zero =>
      cases trm <;> simp [inferCore] at hInfer
    | succ fuel =>
      cases more with
      | zero => cases hFuel
      | succ toFuel =>
        have hFuelTail : fuel ≤ toFuel := Nat.le_of_succ_le_succ hFuel
        cases trm with
        | val value =>
          cases value with
          | lit repr => simpa [inferCore] using hInfer
          | lam body tIn =>
            simp only [inferCore, Outcome.map] at hInfer ⊢
            split at hInfer
            next _ bodyResult hBody =>
              have hBodyTop := ih fuel (Nat.lt_succ_self fuel)
                _ toFuel bodyResult hFuelTail hBody
              simpa only [hBodyTop] using hInfer
            next _ hBody =>
              cases hInfer
        | apply fnTerm arg =>
          cases hFn : fnTerm.inferCore fuel with
          | outOfFuel => simp [inferCore, hFn] at hInfer
          | yield fnResult =>
            cases hArg : arg.inferCore fuel with
            | outOfFuel => simp [inferCore, hFn, hArg] at hInfer
            | yield argResult =>
              have hFnTop := ih fuel (Nat.lt_succ_self fuel)
                fnTerm toFuel fnResult hFuelTail hFn
              have hArgTop := ih fuel (Nat.lt_succ_self fuel)
                arg toFuel argResult hFuelTail hArg
              simpa [inferCore, hFn, hArg, hFnTop, hArgTop] using hInfer
        | ref receipt =>
          cases receipt with
          | inl rc =>
            let executable : Trm refs.ExeParameters := (refs.uid2val.get rc).asTrm
            let original := executable.exe2build
            have hOriginal : original.inferCore fuel = .yield result := by
              simpa [inferCore, executable, original] using hInfer
            have hOriginalTop := ih fuel (Nat.lt_succ_self fuel)
              original toFuel result hFuelTail hOriginal
            simpa [inferCore, executable, original] using hOriginalTop
          | inr rc =>
            cases env.uid2typ.get rc with
            | primitive => simpa [inferCore] using hInfer
            | fn tIn tOut => simpa [inferCore] using hInfer

/-- Value inference monotonicity follows from term inference monotonicity. -/
theorem valueInferMonotone [refs : ExeRefs] [env : BuildEnv refs]
    (value : Val env.BuildParameters) :
    value.asTrm.inferCore.Monotone :=
  termInferMonotone value.asTrm

end AST

end Lp2lc.Active.STLC
