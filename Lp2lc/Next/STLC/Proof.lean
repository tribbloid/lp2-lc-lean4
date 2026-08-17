import «Lp2lc».Next.STLC.STLCDef
import «Lp2lc».Next.STLC.__Infer
import «Lp2lc».Next.STLC.__Infer_Umbral

namespace Lp2lc.Next.STLC

open Lp2lc.Active.Util
open Lp2lc.Active.Util.Rec

namespace AST

/-- Evaluation that succeeds with smaller fuel succeeds with the same value at larger fuel. -/
theorem termEvalMonotone [env : ExeEnv]
    (trm : Trm env.ExeParameters) :
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
                    cases hBody : (body (env.trm2valCtx.inv input)).eval fuel with
                    | outOfFuel =>
                      simp [AST.eval, hFn, hArg, hBody] at hEval
                    | yield bodyResult =>
                      have hBodyTop := ih fuel (Nat.lt_succ_self fuel)
                        (body (env.trm2valCtx.inv input))
                        toFuel bodyResult hFuelTail hBody
                      simpa [AST.eval, hFn, hArg, hFnTop, hArgTop,
                        hBody, hBodyTop] using hEval
        | ref receipt =>
          simpa [AST.eval] using hEval

/-- Inference that succeeds with smaller fuel succeeds with the same type at larger fuel. -/
theorem termInferMonotone [env : BuildEnv]
    (trm : Trm env.BuildParameters) :
    trm.infer.Monotone := by
  intro less more result hFuel hInfer
  induction less using Nat.strongRecOn generalizing trm more result with
  | ind fromFuel ih =>
    cases fromFuel with
    | zero =>
      cases trm <;> simp [AST.infer] at hInfer
    | succ fuel =>
      cases more with
      | zero => cases hFuel
      | succ toFuel =>
        have hFuelTail : fuel ≤ toFuel := Nat.le_of_succ_le_succ hFuel
        cases trm with
        | val value =>
          cases value with
          | lit repr => simpa [AST.infer] using hInfer
          | lam body tIn =>
            simp only [AST.infer, Outcome.map] at hInfer ⊢
            split at hInfer
            next _ bodyResult hBody =>
              have hBodyTop := ih fuel (Nat.lt_succ_self fuel)
                _ toFuel bodyResult hFuelTail hBody
              simpa [hBodyTop] using hInfer
            next _ hBody =>
              cases hInfer
        | apply fnTerm arg =>
          cases hFn : fnTerm.infer fuel with
          | outOfFuel => simp [AST.infer, hFn] at hInfer
          | yield fnResult =>
            cases hArg : arg.infer fuel with
            | outOfFuel => simp [AST.infer, hFn, hArg] at hInfer
            | yield argResult =>
              have hFnTop := ih fuel (Nat.lt_succ_self fuel)
                fnTerm toFuel fnResult hFuelTail hFn
              have hArgTop := ih fuel (Nat.lt_succ_self fuel)
                arg toFuel argResult hFuelTail hArg
              simpa [AST.infer, hFn, hArg, hFnTop, hArgTop] using hInfer
        | ref receipt =>
          cases receipt with
          | inl rc =>
            let original : Val env.BuildParameters :=
              (env.trm2valCtx.get rc).map env.ExeParameters env.BuildParameters (Sum.inl) id
            have hOriginal : original.asTrm.infer fuel = .yield result := by
              simpa [AST.infer, original] using hInfer
            have hOriginalTop := ih fuel (Nat.lt_succ_self fuel)
              original.asTrm toFuel result hFuelTail hOriginal
            simpa [AST.infer, original] using hOriginalTop
          | inr rc =>
            cases env.trm2typCtx.get rc with
            | lit repr => simpa [AST.infer] using hInfer
            | lam body tIn => simpa [AST.infer] using hInfer

/-- Value inference monotonicity follows from term inference monotonicity. -/
theorem valueInferMonotone [env : BuildEnv]
    (value : Val env.BuildParameters) :
    value.asTrm.infer.Monotone :=
  termInferMonotone value.asTrm

end AST

class ProvingEnv extends ProvingBase

namespace Umbral

section variable [env : ProvingEnv]

/-- Mirrors term inference while preserving its selected-fuel correspondence. -/
def infer_prove (trm : AST.Trm env.BuildParameters) (fuel : Nat) : Objective trm fuel :=
  match fuel with
  | 0 => ⟨.outOfFuel, rfl⟩
  | fuel + 1 =>
    match trm with
    | .val (.lit _) => ⟨.yield (some ⟨.primitive⟩), rfl⟩
    | .val (.lam body tIn) =>
      let index : env.BuildParameters.C := .inr (env.trm2typCtx.inv (.lam body tIn))
      let result := infer_prove (body index) fuel
      ⟨result.compilation.map
          (Option.map (λ safety => ⟨.fn tIn safety.typ⟩)), by
        change _ = ((body index).infer fuel).map (Option.map (AST.fn tIn))
        rw [← result.sameInfer]
        cases result.compilation <;>
          simp [Rec.Outcome.map, Function.comp_def]⟩
    | .apply fnTerm arg =>
      let fnResult := infer_prove fnTerm fuel
      let argResult := infer_prove arg fuel
      let applyResult (fnType argType : Rec.Outcome (Option (AST.Typ env.BuildParameters))) :
          Rec.Outcome (Option (AST.Typ env.BuildParameters)) :=
        match fnType, argType with
        | .yield (some (.fn tIn tOut)), .yield (some argTyp) =>
          if argTyp ≤ tIn then .yield (some tOut) else .yield none
        | .outOfFuel, _ => .outOfFuel
        | _, .outOfFuel => .outOfFuel
        | _, _ => .yield none
      let result := applyResult
        (fnResult.compilation.map (Option.map SafetyOf.typ))
        (argResult.compilation.map (Option.map SafetyOf.typ))
      ⟨result.map (Option.map (λ typ => ⟨typ⟩)), by
        have hResult : result = (AST.apply fnTerm arg).infer (fuel + 1) := by
          calc
            result = applyResult
                (fnResult.compilation.map (Option.map SafetyOf.typ))
                (argResult.compilation.map (Option.map SafetyOf.typ)) := rfl
            _ = applyResult
                (fnTerm.infer fuel)
                (arg.infer fuel) := by
              congr 1
              · exact fnResult.sameInfer
              · exact argResult.sameInfer
            _ = (AST.apply fnTerm arg).infer (fuel + 1) := by
              conv =>
                rhs
                unfold AST.infer
                simp only
              dsimp only [applyResult]
              split <;> simp_all
        rw [hResult]
        cases (AST.apply fnTerm arg).infer (fuel + 1) <;>
          simp [Rec.Outcome.map, Function.comp_def]⟩
    | .ref (.inl receipt) =>
      let original : AST.Val env.BuildParameters :=
        (env.trm2valCtx.get receipt).map env.ExeParameters env.BuildParameters (Sum.inl) id
      let result := infer_prove original.asTrm fuel
      ⟨result.compilation.map (Option.map (λ safety => ⟨safety.typ⟩)), by
        change _ = original.asTrm.infer fuel
        rw [← result.sameInfer]
        cases result.compilation <;>
          simp [Rec.Outcome.map, Function.comp_def]⟩
    | .ref (.inr receipt) => by
      cases h : env.trm2typCtx.get receipt with
      | lit repr =>
        exact ⟨.yield (some ⟨.primitive⟩), by
          simp [AST.infer, h, Rec.Outcome.map]⟩
      | lam body tIn =>
        exact ⟨.yield (some ⟨tIn⟩), by
          simp [AST.infer, h, Rec.Outcome.map]⟩

end

end Umbral

end Lp2lc.Next.STLC
