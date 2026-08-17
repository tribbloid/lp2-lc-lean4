import «Lp2lc».Next.STLC.__Infer

namespace Lp2lc.Next.STLC

open Lp2lc.Active.Util

namespace Umbral

section variable [env : ProvingBase]

structure SafetyOf (trm : AST.Trm env.ExeF) where
  typ : AST.Typ env.BuildF
  -- safety : Safety trm typ -- TODO: this lemma has been temporarily disabled. Enable it later.

abbrev Compilation (trm : AST.Trm env.ExeF) :=
  Rec.OutcomeOpt (SafetyOf trm) -- one observation of the semi-decidability of executing term

/-- Requires the proving computation to shadow term inference at the selected fuel. -/
structure Objective (trm : AST.Trm env.ExeF) (fuel : Nat) : Type where
  compilation : Compilation trm
  sameInfer : compilation.map (Option.map SafetyOf.typ) = trm.infer fuel

end

end Umbral

end Lp2lc.Next.STLC