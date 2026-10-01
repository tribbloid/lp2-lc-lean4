import «Lp2lc».Active.STLC.STLCDef
import «Lp2lc».Active.STLC.__Infer

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util
open Lp2lc.Active.Util.Rec

namespace Infer_Proof

def Safety {refs : HasUId2Any} [build : BuildEnv refs] [exe : ExeEnv refs]
    (trm : AST.Trm refs.Parameters) (t2 : AST.Typ refs.Parameters) : Prop :=
  trm.eval.isSemiDecidable
    (λ v =>
      v.asTrm.infer.isDecidable
        (λ t1 => t1 ≤ t2))

/-- A successfully inferred type makes the executable term safe at that type. -/
theorem fundamental {refs} [build : BuildEnv refs] [exe : ExeEnv refs]
    (trm : AST.Trm refs.Parameters) (fuel : Nat)
    (typ : AST.Typ refs.Parameters)
    (hInfer : trm.infer fuel = .yield (some typ)) :
    Safety trm typ := sorry

/--
if compiled a term and succeeded, the term must be safe

TODO: this is the "Paranoid Fundamental theorem": compilation may fail even but term evaluation may succeed
-/
theorem paranoidFundamental {refs} [build : BuildEnv refs] [exe : ExeEnv refs]
    (trm : AST.Trm refs.Parameters) :
    trm.infer.ifSucceedMustSatisfy (
    λ t1 =>
      Safety trm t1
  ) := sorry

end Infer_Proof

end Lp2lc.Active.STLC
