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


/--
Environment required by the soundness/safety theorems of [AST].

Already a subclass of [RuntimeEnv] and [CompilerEnv] through [ProvingBase], thus can reuse their contexts immediately as well as creating its own.

CAUTION: the same [AST] in the above 2 contexts is always mapped to different UIDs:
- in compiletime, UIDs are from type information through [CompilerEnv.trm2typCtx]
- in runtime, UIDs are from runtime values through [RuntimeEnv.trm2valCtx]
New contexts will be required to associate them
-/
class ProvingEnv extends @ProvingBase F

namespace ProvingEnv

-- TODO: add proofCtx here, a new UIDEquiv.Aux should be created (requirements in DEFECT.md). No abstract function is allowed
end ProvingEnv

instance [env: @ProvingEnv F] : @ProvingEnv F := env

section variable [@ProvingEnv F]


/--
like [AST.infer] it inductively infers the [AST.Typ] of a given [AST.Trm], using the structure of [AST.infer] as a blueprint.

unlike [AST.infer] it is obliged to produce a bundle of:

- original [AST.Typ]
- proof that the [AST.Trm2Typ] pair is safe to evaluate ([ProvenCondition], i.e. [Safety])

Agreement with [AST.infer] is not part of the bundle; it is required separately by [Objective.sameInfer].
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
      let index := env.trm2typCtx.getUID ⟨.val (.lam body tIn), tIn⟩
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
