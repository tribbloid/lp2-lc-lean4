import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

namespace AST

/-- Type syntax has no references, so its lexical context can be changed structurally. -/
private def reindex {n m} (self : Typ n) : Typ m :=
  match self with
  | .TLit => .TLit
  | .TFn tIn tOut => .TFn (reindex tIn) (reindex tOut)

/-- Infer a term's type using the caller's known type bindings, without runtime evaluation. -/
def infer {n} (self : Trm n) (bindings : (index : Nat) → Option (Typ index)) : RecOpt (Typ n) := λ fuel =>
  match fuel, self with
  | 0, _ => .outOfFuel
  | _, .val (.lit _) => .yield (some .TLit)
  | _, .ref (lower := lower) _ _ => .yield ((bindings lower).map reindex)
  | fuel + 1, .val (.fn tIn body) =>
    (infer (body.apply .only)
      (λ index => if index = n + 2 then some (reindex tIn)
        else if index = n + 1 then none else bindings index) fuel).map
      (λ out => out.map (λ tOut => .TFn tIn (reindex tOut)))
  | fuel + 1, .apply fn arg =>
    match infer fn bindings fuel, infer arg bindings fuel with
    | .yield (some (.TFn tIn tOut)), .yield (some argTyp) =>
      if argTyp ≤ tIn then .yield (some tOut) else .yield none
    | .yield _, .yield _ => .yield none
    | _, _ => .outOfFuel

/-- Inference that succeeds with smaller fuel succeeds with the same type at larger fuel. -/
theorem termInferMonotone {n} (trm : Trm n) (bindings : (index : Nat) → Option (Typ index)) :
    (infer trm bindings).Monotone := by
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
theorem valueInferMonotone {n} (value : Val n) (bindings : (index : Nat) → Option (Typ index)) :
    (infer value.asTrm bindings).Monotone :=
  termInferMonotone value.asTrm

end AST


end Lp2lc.Active.STLC
