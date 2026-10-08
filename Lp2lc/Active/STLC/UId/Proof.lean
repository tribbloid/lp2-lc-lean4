import «Lp2lc».Active.STLC.UId.InferDef
import «Lp2lc».Active.STLC.UId.Eval

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util EnvBase EnvBase.Trm

/-- A runtime source context, including the free references in its stored function bodies.

Its shared lookups must contain values whose canonical syntax agrees with the transported source
value. This excludes type-only references throughout captured values without assuming their safety.
-/
structure RuntimeContext (refs : UIdRefs) where
  base : EnvBase
  values : KVRefs base.UId base.Val
  embed : base.UId → refs.UId
  compatible : ∀ receipt, (refs.uid2any.get (embed receipt)).elim
    (λ value => Val.Same value (AST.recarrier (values.get receipt) (.mk embed))) (λ _ => False)

section variable {refs : UIdRefs} [build : BuildEnv refs] [exe : ExeEnv refs]

/-- Every completed evaluation succeeds, and its value can be inferred at the claimed type. -/
def Safety (trm : refs.base.Trm) (typ : refs.base.Typ) : Prop :=
  trm.eval.isSemiDecidable
    (λ value => value.asTrm.infer.isDecidable (λ inferred => inferred ≤ typ))

/-- Successful inference makes the same transported runtime source term safe.

The context premise is required: compile-time type receipts alone cannot be evaluated as values.
This is conjecture scaffolding; the soundness proof is intentionally deferred.
-/
theorem fundamental (context : RuntimeContext refs) (trm : context.base.Trm)
    (fuel : Nat) (typ : refs.base.Typ)
    (hInfer : infer (refs := refs) (AST.recarrier trm (.mk context.embed)) fuel = .yield (some typ)) :
    Safety (AST.recarrier trm (.mk context.embed)) typ := sorry

end
end Lp2lc.Active.STLC
