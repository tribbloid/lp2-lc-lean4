import «Lp2lc».Active.STLC.STLCDef
import «Lp2lc».Active.STLC.__Infer

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util
open Lp2lc.Active.Util.Rec

namespace AST

/-- Inference that succeeds with smaller fuel succeeds with the same type at larger fuel. -/
theorem termInferMonotone [refs : HasUId2Any] [env : BuildEnv refs]
    (trm : Trm refs.Parameters) :
    trm.infer.Monotone := by
  intro less more result hFuel hInfer
  induction less using Nat.strongRecOn generalizing trm more result with
  | ind fromFuel ih =>
    cases fromFuel with
    | zero =>
      cases trm <;> simp [infer] at hInfer
    | succ fuel =>
      cases more with
      | zero => cases hFuel
      | succ toFuel =>
        have hFuelTail : fuel ≤ toFuel := Nat.le_of_succ_le_succ hFuel
        cases trm with
        | val value =>
          cases value with
          | lit repr => simpa [infer] using hInfer
          | lam body tIn =>
            simp only [infer, Outcome.map] at hInfer ⊢
            split at hInfer
            next _ bodyResult hBody =>
              have hBodyTop := ih fuel (Nat.lt_succ_self fuel)
                _ toFuel bodyResult hFuelTail hBody
              simpa [hBodyTop] using hInfer
            next _ hBody =>
              cases hInfer
        | apply fnTerm arg =>
          cases hFn : fnTerm.infer fuel with
          | outOfFuel => simp [infer, hFn] at hInfer
          | yield fnResult =>
            cases hArg : arg.infer fuel with
            | outOfFuel => simp [infer, hFn, hArg] at hInfer
            | yield argResult =>
              have hFnTop := ih fuel (Nat.lt_succ_self fuel)
                fnTerm toFuel fnResult hFuelTail hFn
              have hArgTop := ih fuel (Nat.lt_succ_self fuel)
                arg toFuel argResult hFuelTail hArg
              simpa [infer, hFn, hArg, hFnTop, hArgTop] using hInfer
        | ref receipt =>
          cases hRef : refs.uid2any.get receipt with
          | inl value =>
            have hValue : value.asTrm.infer fuel = .yield result := by
              simpa [infer, hRef] using hInfer
            have hValueTop := ih fuel (Nat.lt_succ_self fuel)
              value.asTrm toFuel result hFuelTail hValue
            simpa [infer, hRef] using hValueTop
          | inr typ => simpa [infer, hRef] using hInfer

/-- Value inference monotonicity follows from term inference monotonicity. -/
theorem valueInferMonotone [refs : HasUId2Any] [env : BuildEnv refs]
    (value : Val refs.Parameters) :
    value.asTrm.infer.Monotone :=
  termInferMonotone value.asTrm

end AST

/-- A successfully inferred type makes the executable term safe at that type. -/
theorem fundamental {refs} [build : BuildEnv refs] [exe : ExeEnv refs]
    (trm : AST.Trm (ExeEnv.Parameters exe)) (fuel : Nat)
    (typ : AST.Typ refs.Parameters)
    (hInfer :
      (AST.recarrier (Q := refs.Parameters) trm exe.uid2val.upcastK.toFun id).infer fuel =
        .yield (some typ)) :
    Safety trm typ := sorry

/--
if compiled a term and succeeded, the term must be safe

TODO: this is the "Paranoid Fundamental theorem": compilation may fail even but term evaluation may succeed
-/
theorem paranoidFundamental {refs} [build : BuildEnv refs] [exe : ExeEnv refs]
    (trm : AST.Trm (ExeEnv.Parameters exe)) :
    (AST.recarrier (Q := refs.Parameters) trm exe.uid2val.upcastK.toFun id).infer.ifSucceedMustSatisfy (
    λ t1 =>
      Safety trm t1
  ) := sorry

end Lp2lc.Active.STLC
