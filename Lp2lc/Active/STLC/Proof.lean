import «Lp2lc».Active.STLC.STLCDef
import «Lp2lc».Active.STLC.__Infer
import «Lp2lc».Active.STLC.__Infer_umbral

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util
open Lp2lc.Active.Util.Rec

namespace AST

/-- Evaluation that succeeds with smaller fuel succeeds with the same value at larger fuel. -/
theorem termEvalMonotone [core : EnvCore] [env : ExeEnv core]
    (trm : Trm core.ExeParameters) :
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
                    cases hBody : (body (s := ⟨id⟩) (env.uid2valCtx.inv input)).eval fuel with
                    | outOfFuel =>
                      simp [AST.eval, hFn, hArg, hBody] at hEval
                    | yield bodyResult =>
                      have hBodyTop := ih fuel (Nat.lt_succ_self fuel)
                        (body (s := ⟨id⟩) (env.uid2valCtx.inv input))
                        toFuel bodyResult hFuelTail hBody
                      simpa [AST.eval, hFn, hArg, hFnTop, hArgTop,
                        hBody, hBodyTop] using hEval
        | ref receipt =>
          simpa [AST.eval] using hEval

/-- Inference that succeeds with smaller fuel succeeds with the same type at larger fuel. -/
theorem termInferMonotone [core : EnvCore] [env : BuildEnv core]
    (trm : Trm env.BuildParameters) : -- TODO: this is actually a theorem for `infer_core`
    trm.infer_core.Monotone := by
  intro less more result hFuel hInfer
  induction less using Nat.strongRecOn generalizing trm more result with
  | ind fromFuel ih =>
    cases fromFuel with
    | zero =>
      cases trm <;> simp [infer_core] at hInfer
    | succ fuel =>
      cases more with
      | zero => cases hFuel
      | succ toFuel =>
        have hFuelTail : fuel ≤ toFuel := Nat.le_of_succ_le_succ hFuel
        cases trm with
        | val value =>
          cases value with
          | lit repr => simpa [infer_core] using hInfer
          | lam body tIn =>
            simp only [infer_core, Outcome.map] at hInfer ⊢
            split at hInfer
            next _ bodyResult hBody =>
              have hBodyTop := ih fuel (Nat.lt_succ_self fuel)
                _ toFuel bodyResult hFuelTail hBody
              simpa [hBodyTop] using hInfer
            next _ hBody =>
              cases hInfer
        | apply fnTerm arg =>
          cases hFn : fnTerm.infer_core fuel with
          | outOfFuel => simp [infer_core, hFn] at hInfer
          | yield fnResult =>
            cases hArg : arg.infer_core fuel with
            | outOfFuel => simp [infer_core, hFn, hArg] at hInfer
            | yield argResult =>
              have hFnTop := ih fuel (Nat.lt_succ_self fuel)
                fnTerm toFuel fnResult hFuelTail hFn
              have hArgTop := ih fuel (Nat.lt_succ_self fuel)
                arg toFuel argResult hFuelTail hArg
              simpa [infer_core, hFn, hArg, hFnTop, hArgTop] using hInfer
        | ref receipt =>
          cases receipt with
          | inl rc =>
            let original : Val env.BuildParameters :=
              (core.uid2val.get rc).map (F := core.ExeParameters) (G := env.BuildParameters) (Sum.inl) id
            have hOriginal : original.asTrm.infer_core fuel = .yield result := by
              simpa [infer_core, original] using hInfer
            have hOriginalTop := ih fuel (Nat.lt_succ_self fuel)
              original.asTrm toFuel result hFuelTail hOriginal
            simpa [infer_core, original] using hOriginalTop
          | inr rc =>
            cases env.uid2typ.get rc with
            | primitive => simpa [infer_core] using hInfer
            | fn tIn tOut => simpa [infer_core] using hInfer

/-- Value inference monotonicity follows from term inference monotonicity. -/
theorem valueInferMonotone [core : EnvCore] [env : BuildEnv core]
    (value : Val env.BuildParameters) :
    value.asTrm.infer_core.Monotone :=
  termInferMonotone value.asTrm

end AST

end Lp2lc.Active.STLC
