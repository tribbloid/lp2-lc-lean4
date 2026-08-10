import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.STLC.__Infer

namespace Lp2lc.Active

namespace STLC

/- this file doesn't need any test -/

open Lp2lc.Active.Util

section variable {F : Free}

namespace Umbral

section variable [@ProvingBase F]

structure SafetyOf (trm : AST.Trm F) where
  typ : AST.Typ F
  -- safety : Safety trm typ -- TODO: this lemma has been temporarily disabled. Enable it later.

abbrev Compilation (trm : AST.Trm F) :=
  Rec.OutcomeOpt (SafetyOf trm) -- one observation of the semi-decidability of executing term

/-- Requires the proving computation to shadow term inference at the selected fuel. -/
structure Objective (trm : AST.Trm F) (fuel : Nat) : Type where
  compilation : Compilation trm
  sameInfer : compilation.map (Option.map SafetyOf.typ) = trm.infer fuel

end

/--
contains a FBound store to save/load intermediate safety proof for both [AST.Trm] and [AST.Val]

[infer_prove] & any theorem that relies on safety can use it, this is the only correspondence between compiletime and runtime variables.
-/
class ProvingEnv extends @ProvingBase F where


namespace ProvingEnv
-- TODO: add proofCtx here, a new Aux0 should be created. No abstract function is allowed

/-- Temporary proof context preserving each stored term-type pair at its reference. -/
abbrev proofCtx (env : @ProvingEnv F) :=
  env.mkAux0 env.trm2typCtx (λ t => SafetyOf (.ref (env.trm2typCtx.getUID t)))

-- all declarations of Fixpoint and it's dependently typed instance should be in this namespace
end ProvingEnv

section

/-- Mirrors term inference while routing typed binders through the temporary proof context.

like [AST.infer] it inductively infer [AST.Typ] of a given [AST.Trm], using the structure of [AST.infer] as a blueprint.

unlike [AST.infer] it is obliged to produce a [Objective] bundle of:

- original [AST.Typ]
- proof that it has the same result to [AST.infer]

Recommendation:

- create a [UIDEquiv.Aux0] from trm2TypCtx (Aux0 contains an abuse that allows other UID to be used to get any value, it is temporarily tolerated)
- write an algorithm identical with Trm.infer, but save into [UIDEquiv.Aux0] instead to get an UID

-/
def infer_prove [env: @ProvingEnv F] (trm : AST.Trm F) (fuel : Nat) : Objective trm fuel :=
  match fuel with
  | 0 => ⟨.outOfFuel, rfl⟩
  | fuel + 1 =>
    match trm with
    | .val (.lit _) => ⟨.yield (some ⟨.primitive⟩), rfl⟩
    | .val (.lam body tIn) =>
      let index := env.trm2typCtx.getUID ⟨.val (.lam body tIn), tIn⟩; let result := infer_prove (body index) fuel
      ⟨result.compilation.map (Option.map (λ safety => ⟨.fn tIn safety.typ⟩)), by
        calc
          _ = (result.compilation.map (Option.map SafetyOf.typ)).map (Option.map (AST.fn tIn)) := by
            cases result.compilation <;> simp [Rec.Outcome.map, Function.comp_def]
          _ = ((body index).infer fuel).map (Option.map (AST.fn tIn)) := by rw [result.sameInfer]
          _ = (AST.val (.lam body tIn)).infer (fuel + 1) := rfl⟩
    | .apply fnTerm arg =>
      let fnResult := infer_prove fnTerm fuel
      let argResult := infer_prove arg fuel
      let result : Rec.Outcome (Option (AST.Typ F)) :=
        match fnResult.compilation.map (Option.map SafetyOf.typ), argResult.compilation.map (Option.map SafetyOf.typ) with
        | .yield (some (.fn tIn tOut)), .yield (some argTyp) =>
          if argTyp ≤ tIn then .yield (some tOut) else .yield none
        | .outOfFuel, _ => .outOfFuel
        | _, .outOfFuel => .outOfFuel
        | _, _ => .yield none
      ⟨result.map (Option.map (λ typ => ⟨typ⟩)), by
        have hResult : result = (AST.apply fnTerm arg).infer (fuel + 1) := by
          simp only [result, AST.infer]
          rw [fnResult.sameInfer, argResult.sameInfer] <;> rfl
        rw [hResult]
        cases (AST.apply fnTerm arg).infer (fuel + 1) <;> simp [Rec.Outcome.map, Function.comp_def]⟩
    | @AST.ref _ uid => ⟨.yield (some ⟨(env.trm2typCtx.inv uid).typ⟩), rfl⟩

end

end Umbral
end

end STLC
