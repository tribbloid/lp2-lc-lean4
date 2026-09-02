import «Lp2lc».Active.STLC.__Infer

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

namespace Umbral

structure TypeWithSafey {refs} [build : BuildEnv refs]
    (trm : AST.Trm refs.Parameters) where
  t2 : AST.Typ refs.Parameters
  safety : [_exe : ExeEnv refs] -> Safety trm t2

class ProvingEnv (refs : TypOrValRefs) extends BuildEnv refs where
  --TODO: this impl should be final, move into namespace
  uid2typWithSafetyCtx : UIdEquiv.Lesser (base := refs.uid2either)
    (λ value : PSigma (λ trm : AST.Trm refs.Parameters => TypeWithSafey trm) =>
      Sum.inr value.snd.t2)

namespace ProvingEnv


end ProvingEnv




/-
This is an agumented version of [AST.Trm.infer].

There is only 1 difference: it must produce a type judge with safety proof that trm always evaluate to a value of the same type

It also has access to [ProvingEnv], a mirror of [BuildEnv] with [uid2typWithSafetyCtx] : an extra equivalence between type with safety proof and a subtype of UId

TODO: discharge this function.
- The execution of `Trm.infer` should yield identical `TypeWithSafey.t2` without safety proof
- If the original `Trm.infer` is unsafe, revise it to be safe first
- You are allowed to add more context into ProvingEnv namespace to meet proving demand
-/
/-- Infers build types for executable terms. -/
def infer [refs : TypOrValRefs] [proving : ProvingEnv refs] [env : ExeEnv refs]
    (trm : AST.Trm refs.Parameters) :
    RecOpt (TypeWithSafey trm) := sorry

end Umbral

end Lp2lc.Active.STLC
