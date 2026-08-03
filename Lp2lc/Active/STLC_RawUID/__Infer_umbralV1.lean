import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.STLC.__Infer

namespace Lp2lc.Active

namespace STLC
open Lp2lc.Active.Util

section variable {F : Free}

namespace Umbral

section variable [@ProvingBase F]

structure ProvenCondition (trm2typ: AST.Trm2Typ F) : Type where
  sameInfer: trm2typ.trm.infer.isDecidable (λ t2 => trm2typ.typ <= t2)
  safety: Safety trm2typ.trm trm2typ.typ

end

/--
contains a [UIDEquiv.Aux] store for intermediate safety proofs over both `AST.Trm` and `AST.Val`

`infer_prove` & any theorem that relies on safety can use it, this is the only correspondence between compiletime and runtime variables.
-/
class ProvingEnv where
  base: @ProvingBase F
  proofCtx : base.trm2typCtx.Aux (λ t => ProvenCondition t)

instance [env: @ProvingEnv F] : @ProvingBase F := env.base

section variable [@ProvingEnv F]

/--
like `Trm.infer` it inductively infer `Typ` of a given `Trm`, using the structure of `Trm.infer` as a blueprint.

unlike `Trm.infer` it is obliged to produce a `ProvenCondition` bundle of:

- original `Typ`
- proof that it has the same result to `Trm.infer`
- proof that the `Trm : Typ` pair is safe to evaluate
-/
def infer_prove [env: @ProvingEnv F] (trm : AST.Trm F) :
    RecOption (PSigma (λ typ : AST.Typ F => @ProvenCondition F env.base ⟨trm, typ⟩)) :=
  λ
  | 0 => .outOfFuel
  | fuel + 1 =>
    let proven (term : AST.Trm F) (typ : AST.Typ F)
        (condition : @ProvenCondition F env.base ⟨term, typ⟩) :
        @ProvenCondition F env.base ⟨term, typ⟩ := by
      let id := env.base.trm2typCtx.getUID ⟨term, typ⟩
      simpa [id] using env.proofCtx.invEv ⟨id, env.proofCtx.getEv ⟨⟨term, typ⟩, condition⟩⟩
    match trm with
    | .val (.primitive repr) =>
      .yield (some ⟨.primitive, proven (.val (.primitive repr)) .primitive
        { sameInfer := by
            refine ⟨1, ?_⟩
            simp [AST.Trm.infer]
            rfl
          safety := by
            unfold Safety
            intro runtimeFuel
            cases runtimeFuel with
            | zero => simp [AST.Trm.eval]
            | succ runtimeFuel =>
              simp [AST.Trm.eval, AST.Trm.CanInhabit]
              exact ⟨1, by
                simp [AST.Trm.infer]
                rfl⟩ }⟩)
    | .val (.fn body tIn) =>
      let index := env.base.trm2typCtx.getUID ⟨.val (.fn body tIn), tIn⟩
      ((infer_prove (body index)) fuel).map (λ out =>
        out.bind (λ result =>
          some ⟨.fn tIn result.fst, proven (.val (.fn body tIn)) (.fn tIn result.fst)
            { sameInfer := by
                rcases result.snd.sameInfer with ⟨bodyFuel, hBodyInfer⟩
                refine ⟨bodyFuel + 1, ?_⟩
                cases hBody : (body index).infer bodyFuel with
                | outOfFuel => simp [hBody] at hBodyInfer
                | yield out =>
                    cases out with
                    | none => simp [hBody] at hBodyInfer
                    | some tOut' =>
                      simp [hBody] at hBodyInfer
                      have htOutEq : result.fst = tOut' := hBodyInfer
                      simp [AST.Trm.infer, index, hBody, htOutEq]
                      rfl
              safety := by
                unfold Safety
                intro runtimeFuel
                cases runtimeFuel with
                | zero => simp [AST.Trm.eval]
                | succ runtimeFuel =>
                  simp [AST.Trm.eval, AST.Trm.CanInhabit]
                  rcases result.snd.sameInfer with ⟨bodyFuel, hBodyInfer⟩
                  refine ⟨bodyFuel + 1, ?_⟩
                  cases hBody : (body index).infer bodyFuel with
                  | outOfFuel => simp [hBody] at hBodyInfer
                  | yield out =>
                      cases out with
                      | none => simp [hBody] at hBodyInfer
                      | some tOut' =>
                        simp [hBody] at hBodyInfer
                        have htOutEq : result.fst = tOut' := hBodyInfer
                        simp [AST.Trm.infer, index, hBody, htOutEq]
                        rfl
            }⟩))
    | .apply fn arg =>
      match (infer_prove fn) fuel, (infer_prove arg) fuel with
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none
    | @AST.Trm.ref _ i =>
      .yield none

-- theorem termInferMonotone [env : @ProvingEnv F]
--     (trm : AST.Trm F) :
--      (infer trm).Monotone := sorry


-- def eval_prove [env: @ProvingEnv F] (trm: AST.Trm F): RecOptionn ()

end

end Umbral
end

end STLC
