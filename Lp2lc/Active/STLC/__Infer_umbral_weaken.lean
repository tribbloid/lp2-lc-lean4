import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.STLC.__Infer

namespace Lp2lc.Active

namespace STLC
open Lp2lc.Active.Util

section variable {F : Free}

namespace Umbral

section variable [@ProvingBase F]

structure SafetyOf (trm : AST.Trm F) where
  typ : AST.Typ F
  -- safety : Safety trm typ -- TODO: this lemma has been temporarily disabled. Enable it later.

abbrev Compilation (trm : AST.Trm F) :=
  RecOption (SafetyOf trm) -- namely, the semi-decidability of executing term

/-- Requires the proving computation to shadow every outcome of term inference. -/
structure Objective (trm : AST.Trm F) (fuel : Nat) : Type where
  compilation : Compilation trm fuel
  sameInfer : (compilation fuel).map (Option.map SafetyOf.typ) = trm.infer fuel

end

/--
contains a FBound store to save/load intermediate safety proof for both [AST.Trm] and [AST.Val]

[infer_prove] & any theorem that relies on safety can use it, this is the only correspondence between compiletime and runtime variables.
-/
class ProvingEnv extends @ProvingBase F where


namespace ProvingEnv
-- TODO: add proofCtx here, a new Aux0 should be created. No abstract function is allowed

/-- Temporary typed-reference store for the weakened objective. -/
abbrev proofCtx (env : @ProvingEnv F) :
    UIDEquiv.Aux0 env.trm2typCtx (λ _ => AST.Typ F) where
  invEv uid := (env.trm2typCtx.inv uid).typ

-- all declarations of Fixpoint and it's dependently typed instance should be in this namespace
end ProvingEnv

section

/-- Mirrors term inference while routing typed binders through the temporary proof context. -/
private def inferTyp [env : @ProvingEnv F] (trm : AST.Trm F) (fuel : Nat) :
    { result : Rec.Outcome (Option (AST.Typ F)) // result = trm.infer fuel } :=
  match fuel with
  | 0 => ⟨.outOfFuel, rfl⟩
  | fuel + 1 =>
    match trm with
    | .val (.lit _) => ⟨.yield (some .primitive), rfl⟩
    | .val (.lam body tIn) =>
      let index := env.proofCtx.getEv ⟨⟨.val (.lam body tIn), tIn⟩, tIn⟩
      let result := inferTyp (body index) fuel
      ⟨result.val.map (Option.map (AST.fn tIn)), by
        rw [result.property] <;> rfl⟩
    | .apply fnTerm arg =>
      let fnResult := inferTyp fnTerm fuel
      let argResult := inferTyp arg fuel
      ⟨match fnResult.val, argResult.val with
        | .yield (some (.fn tIn tOut)), .yield (some argTyp) =>
          if argTyp ≤ tIn then .yield (some tOut) else .yield none
        | .outOfFuel, _ => .outOfFuel
        | _, .outOfFuel => .outOfFuel
        | _, _ => .yield none,
        by
          simp only [AST.infer]
          rw [fnResult.property, argResult.property]
          cases fnTerm.infer fuel <;> cases arg.infer fuel <;> rfl⟩
    | @AST.ref _ uid => ⟨.yield (some (env.proofCtx.invEv uid)), rfl⟩

/--
like [AST.infer] it inductively infer [AST.Typ] of a given [AST.Trm], using the structure of [AST.infer] as a blueprint.

unlike [AST.infer] it is obliged to produce a [Objective] bundle of:

- original [AST.Typ]
- proof that it has the same result to [AST.infer]

Recommendation:

- create a [UIDEquiv.Aux0] from trm2TypCtx (Aux0 contains an abuse that allows other UID to be used to get any value, it is temporarily tolerated)
- write an algorithm identical with Trm.infer, but save into [UIDEquiv.Aux0] instead to get an UID

-/
def infer_prove [env: @ProvingEnv F] (trm : AST.Trm F) (fuel : Nat) : Objective trm fuel :=
  {
    compilation := λ fuel => (inferTyp trm fuel).val.map (Option.map (λ typ => ⟨typ⟩))
    sameInfer := λ fuel => by
      rw [(inferTyp trm fuel).property]
      cases trm.infer fuel <;> simp [Rec.Outcome.map, Function.comp_def]
  }

end

end Umbral
end

end STLC
