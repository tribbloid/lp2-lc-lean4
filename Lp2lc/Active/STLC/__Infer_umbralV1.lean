import «Lp2lc».Active.STLC.STLCDef
import «Lp2lc».Active.STLC.__Infer

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util
open Lp2lc.Active.Util.Rec

namespace UmbralV1

section variable [core : EnvCore] [env : BuildEnv core]

structure SafetyOf (trm : AST.Trm env.BuildParameters) where
  typ : AST.Typ env.BuildParameters
  -- safety : Safety trm typ -- TODO: this lemma has been temporarily disabled. Enable it later.

abbrev Compilation (trm : AST.Trm env.BuildParameters) :=
  Rec.OutcomeOpt (SafetyOf trm) -- one observation of the semi-decidability of executing term

/-- Requires the proving computation to shadow term inference at the selected fuel. -/
structure Objective (trm : AST.Trm env.BuildParameters) (fuel : Nat) : Type 2 where
  compilation : Compilation trm
  sameInfer : compilation.map (Option.map SafetyOf.typ) = trm.infer_core fuel

/-- Mirrors term inference while preserving its selected-fuel correspondence. -/
def infer_prove (trm : AST.Trm env.BuildParameters) (fuel : Nat) : Objective trm fuel :=
  match fuel with
  | 0 => ⟨.outOfFuel, rfl⟩
  | fuel + 1 =>
    match trm with
    | .val (.lit _) => ⟨.yield (some ⟨.primitive⟩), rfl⟩
    | .val (.lam body tIn) =>
      let index : env.BuildParameters.C := .inr (env.trm2typCtx.inv tIn)
      let result := infer_prove (body (s := ⟨id⟩) index) fuel
      ⟨result.compilation.map
          (Option.map (λ safety => ⟨.fn tIn safety.typ⟩)), by
        change _ = ((body (s := ⟨id⟩) index).infer_core fuel).map (Option.map (AST.fn tIn))
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
        have hResult : result = (AST.apply fnTerm arg).infer_core (fuel + 1) := by
          calc
            result = applyResult
                (fnResult.compilation.map (Option.map SafetyOf.typ))
                (argResult.compilation.map (Option.map SafetyOf.typ)) := rfl
            _ = applyResult
                (fnTerm.infer_core fuel)
                (arg.infer_core fuel) := by
              congr 1
              · exact fnResult.sameInfer
              · exact argResult.sameInfer
            _ = (AST.apply fnTerm arg).infer_core (fuel + 1) := by
              conv =>
                rhs
                unfold AST.infer_core
                simp only
              dsimp only [applyResult]
              split <;> simp_all
        rw [hResult]
        cases (AST.apply fnTerm arg).infer_core (fuel + 1) <;>
          simp [Rec.Outcome.map, Function.comp_def]⟩
    | .ref (.inl receipt) =>
      let original : AST.Val env.BuildParameters :=
        (core.trm2val.get receipt).map (F := core.ExeParameters) (G := env.BuildParameters) (Sum.inl) id
      let result := infer_prove original.asTrm fuel
      ⟨result.compilation.map (Option.map (λ safety => ⟨safety.typ⟩)), by
        change _ = original.asTrm.infer_core fuel
        rw [← result.sameInfer]
        cases result.compilation <;>
          simp [Rec.Outcome.map, Function.comp_def]⟩
    | .ref (.inr receipt) => by
      cases h : env.trm2typ.get receipt with
      | primitive =>
        exact ⟨.yield (some ⟨.primitive⟩), by
          simp [AST.infer_core, h, Rec.Outcome.map]⟩
      | fn tIn tOut =>
        exact ⟨.yield (some ⟨.fn tIn tOut⟩), by
          simp [AST.infer_core, h, Rec.Outcome.map]⟩

end

end UmbralV1

end Lp2lc.Active.STLC
