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
  safety: Safety trm2typ.trm trm2typ.typ -- TODO: should this objective be delayed?

end

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
def infer_prove [env: @ProvingEnv F] (trm : AST.Trm F) :
    RecOption (PSigma (λ typ : AST.Typ F => @ProvenCondition F env.base ⟨trm, typ⟩)) :=
  λ
  | 0 => .outOfFuel
  | fuel + 1 =>
    let proven (term : AST.Trm F) (typ : AST.Typ F) :
        @ProvenCondition F env.base ⟨term, typ⟩ := by
      simpa using
        env.proofCtx.loadMetadata (env.base.trm2typCtx.save ⟨term, typ⟩)
    match trm with
    | .val (.primitive repr) =>
      .yield (some ⟨.primitive, proven (.val (.primitive repr)) .primitive⟩)
    | .val (.fn body tIn) =>
      let index := env.base.trm2typCtx.save ⟨trm, tIn⟩
      ((infer_prove (body index)) fuel).map (λ out =>
        out.map (λ result =>
          ⟨.fn tIn result.fst,
            proven (.val (.fn body tIn)) (.fn tIn result.fst)⟩))
    | .apply fn arg =>
      match (infer_prove fn) fuel, (infer_prove arg) fuel with
      | .yield (some ⟨.fn tIn tOut, _⟩), .yield (some ⟨argTyp, _⟩) =>
        if argTyp ≤ tIn then
          .yield (some ⟨tOut, proven (.apply fn arg) tOut⟩)
        else .yield none
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none
    | @AST.Trm.ref _ i =>
      let typ := (env.base.trm2typCtx.load i).typ
      .yield (some ⟨typ, proven (.ref i) typ⟩)

-- theorem termInferMonotone [env : @ProvingEnv F]
--     (trm : AST.Trm F) :
--      (infer trm).Monotone := sorry


-- def eval_prove [env: @ProvingEnv F] (trm: AST.Trm F): RecOptionn ()

end

end Umbral
end

end STLC
