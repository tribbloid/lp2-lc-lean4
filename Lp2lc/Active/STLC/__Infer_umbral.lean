import «Lp2lc».Active.STLC.__Infer

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

namespace Umbral

structure TypeWithSafey {refs} [build : BuildEnv refs] [exe : ExeEnv refs]
    (trm : AST.Trm (ExeEnv.Parameters exe)) where
  t2 : AST.Typ refs.Parameters
  safety : Safety trm t2

class ProvingEnv (refs : HasUId2Any) [exe : ExeEnv refs] extends BuildEnv refs where
  --TODO: this impl should be final, move into namespace
  uid2typWithSafety (trm : AST.Trm (ExeEnv.Parameters exe)) :
    refs.uid2any.Lesser refs.UId (TypeWithSafey trm)
  uid2typWithSafetyCtx (trm : AST.Trm (ExeEnv.Parameters exe)) :
    KVEquiv (uid2typWithSafety trm).toKVRefs

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
def infer [refs : HasUId2Any] [env : ExeEnv refs] [proving : ProvingEnv refs]
    (trm : AST.Trm (ExeEnv.Parameters env)) :
    RecOpt (TypeWithSafey trm) := sorry

end Umbral

end Lp2lc.Active.STLC
