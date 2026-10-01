import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

/--
Adds the compile-time typing context; the shared value-or-type view permits
only lookups, so compile-time code cannot mint receipts from new values.
-/
class BuildEnv (refs : HasUId2Any) where
  uid2typ : refs.uid2any.Lesser refs.UId (AST.Typ refs.Parameters)
  uid2typCtx : KVEquiv uid2typ.toKVRefs -- comparing to ExeEnv, it lose the ability to save value but gain the ability to save type

namespace BuildEnv
section variable {refs : HasUId2Any} (self : BuildEnv refs)

end
end BuildEnv

namespace AST

/--
Infers types from the shared value-or-type reference view.

Value references are inferred recursively, while type references are returned
directly. Compile-time code can read both payloads but can mint only type
receipts through [BuildEnv.uid2typCtx].

WARNING: this function should have no access to ExeEnv! Executing in compile time is strictly prohibited
-/
def infer {refs : HasUId2Any} [env : BuildEnv refs]
    (self : Trm refs.Parameters) : RecOpt (Typ refs.Parameters)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value =>
      match value with
      | .lit _ => .yield (some .TLit)
      | .fn body tIn =>
        let receipt := env.uid2typCtx.inv tIn
        ((body.apply receipt).infer fuel).map
          (λ out => out.map (λ tOut => .TFn tIn tOut))
    | .apply fnTerm arg =>
      let anf := (infer fnTerm fuel, infer arg fuel)
      match anf with
      | (.yield (some (.TFn tIn tOut)), .yield (some argTyp)) =>
        if argTyp ≤ tIn then .yield (some tOut) else .yield none
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .yield none
    | .ref receipt =>
      match refs.uid2any.get receipt with
      | .inl value => value.asTrm.infer fuel
      | .inr typ => .yield (some typ)

-- TODO: remove, not useful
def CanInhabit {refs : HasUId2Any} [env : BuildEnv refs]
    (trm : Trm refs.Parameters) (t2 : Typ refs.Parameters) : Prop :=
  trm.infer.isDecidable (λ t1 => t1 ≤ t2)

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
          | fn body tIn =>
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


end Lp2lc.Active.STLC
