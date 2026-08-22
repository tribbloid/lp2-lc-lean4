import «Lp2lc».Active.STLC.__Infer

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

namespace Umbral

structure TypeWithSafey {refs} [build : BuildEnv refs]
    (trm : AST.Trm refs.ExeParameters) where
  t2 : AST.Typ build.BuildParameters
  safety : [_exe : ExeEnv refs] -> Safety trm t2

class ProvingEnv (refs : ExeRefs) extends BuildEnv refs where
  uid2typWithSafetyCtx :=
    toBuildEnv.uid2typCtx.mkLesser
      (λ _v => PSigma (λ (trm : AST.Trm refs.ExeParameters) => TypeWithSafey (build := toBuildEnv) trm))

/-
This is an agumented version of [AST.Trm.infer].

There is only 1 difference: it must produce a type judge with safety proof that trm always evaluate to a value of the same type

It also has access to [ProvingEnv], a mirror of [BuildEnv] with [uid2typWithSafetyCtx] : an extra equivalence between type with safety proof and a subtype of UId

You are also encouraged to make more context to meet proving demand

TODO: discharge this function.
-/
/-- Infers build types for executable terms. -/
def infer [refs : ExeRefs] [proving : ProvingEnv refs] [env : ExeEnv refs]
    (trm : AST.Trm refs.ExeParameters) : RecOpt (TypeWithSafey trm) := sorry

end Umbral

end Lp2lc.Active.STLC
