import «Lp2lc».Next.STLC.__Infer

namespace Lp2lc.Next.STLC

open Lp2lc.Active.Util

namespace Umbral

section variable [env : ProvingBase]

structure SafetyOf (trm : AST.Trm env.BuildParameters) where
  typ : AST.Typ env.BuildParameters
  -- safety : Safety trm typ -- TODO: this lemma has been temporarily disabled. Enable it later.

abbrev Compilation (trm : AST.Trm env.BuildParameters) :=
  Rec.OutcomeOpt (SafetyOf trm) -- one observation of the semi-decidability of executing term

/-- Requires the proving computation to shadow term inference at the selected fuel. -/
structure Objective (trm : AST.Trm env.BuildParameters) (fuel : Nat) : Type 2 where
  compilation : Compilation trm
  sameInfer : compilation.map (Option.map SafetyOf.typ) = trm.infer fuel

end

end Umbral

end Lp2lc.Next.STLC
