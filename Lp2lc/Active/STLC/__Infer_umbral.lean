import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.STLC.__Infer

namespace Lp2lc.Active

namespace STLC
open Lp2lc.Active.Util

section variable {F : Free}

namespace Umbral

section variable [@ProvingBase F]

abbrev ProvenCondition (trm2typ: AST.Trm2Typ F) : Prop :=
  Safety trm2typ.trm trm2typ.typ -- TODO: should this objective be delayed?

abbrev ProvingResult (trm : AST.Trm F) :=
  RecOption (PSigma (λ typ : AST.Typ F => ProvenCondition ⟨trm, typ⟩))

/-- Requires the proving computation to shadow every outcome of term inference. -/
structure Objective (trm : AST.Trm F) : Type where
  proving : ProvingResult trm
  sameInfer : ∀ (fuel : Nat),
    (proving fuel).map (Option.map PSigma.fst) = trm.infer fuel

end

-- namespace V2

-- structure ProvenCondition (trm: AST.Trm F) : Type where
--   typ : AST.Typ F
--   safety: Safety trm typ

-- class ProvingEnv where
--   base: @ProvingBase F
--   safetyCtx : base.trm2typCtx.Aux (λ trm2typ =>
--     Safety trm2typ.trm trm2typ.typ)

-- /--
-- the objective of infer_proveV2 contains 2 parts:
-- - recursive algorithm that may produce one of the 3 consequences:
--   - successful result
--   - error
--   - out-of-fuel
-- - in **all 3** consequences, the algorithm must yield the same result as trm.infer
-- -/
-- structure ProvingObjective (trm: AST.Trm F) where
--   proving : RecOption (ProvenCondition trm)
--   sameResult: ∀ (fuel : Nat),
--     (proving fuel).map (λ result => result.map (λ condition => condition.typ)) =
--       trm.infer fuel

-- end V2

/--
contains a FBound store to save/load intermediate safety proof for both `AST.Trm` and `AST.Val`

`infer_prove` & any theorem that relies on safety can use it, this is the only correspondence between compiletime and runtime variables.
-/
class ProvingEnv where
  base: @ProvingBase F

namespace ProvingEnv
-- TODO: add proofCtx here, a new Aux0 should be created. No abstract function is allowed
end ProvingEnv

instance [env: @ProvingEnv F] : @ProvingBase F := env.base

section variable [@ProvingEnv F]


/--
like `Trm.infer` it inductively infer `Typ` of a given `Trm`, using the structure of `Trm.infer` as a blueprint.

unlike `Trm.infer` it is obliged to produce a `ProvenCondition` bundle of:

- original `Typ`
- proof that it has the same result to `Trm.infer`
- proof that the `Trm : Typ` pair is safe to evaluate
-/
def infer_prove [env: @ProvingEnv F] (trm : AST.Trm F) : ProvingResult trm :=
  λ
  | 0 => .outOfFuel
  | fuel + 1 =>
    match trm with
    | .val (.lit repr) =>
      .yield (some ⟨.primitive, by
        unfold ProvenCondition Safety
        intro runtimeFuel
        cases runtimeFuel with
        | zero => simp [AST.eval]
        | succ runtimeFuel =>
          simp [AST.eval, AST.CanInhabit]
          exact ⟨1, by
            simp [AST.infer]
            rfl⟩⟩)
    | .val (.lam body tIn) =>
      let index := env.base.trm2typCtx.getUID ⟨.val (.lam body tIn), tIn⟩
      match (infer_prove (body index)) fuel with
      | .outOfFuel => .outOfFuel
      | .yield none => .yield none
      | .yield (some _) =>
        match hInfer : (body index).infer fuel with
        | .outOfFuel => .outOfFuel
        | .yield none => .yield none
        | .yield (some tOut) =>
          .yield (some ⟨.fn tIn tOut, by
            unfold ProvenCondition Safety
            intro runtimeFuel
            cases runtimeFuel with
            | zero => simp [AST.eval]
            | succ runtimeFuel =>
              simp [AST.eval, AST.CanInhabit]
              refine ⟨fuel + 1, ?_⟩
              simp [AST.infer, index, hInfer, Rec.Outcome.map]
              rfl⟩)
    | .apply fn arg =>
      match (infer_prove fn) fuel, (infer_prove arg) fuel with
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none
    | @AST.ref _ _ => .yield none

-- theorem termInferMonotone [env : @ProvingEnv F]
--     (trm : AST.Trm F) :
--      (infer trm).Monotone := sorry


end

end Umbral
end

end STLC
