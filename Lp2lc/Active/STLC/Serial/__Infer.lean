import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util
namespace AST

/-- Convert a known type to the result context, consuming fuel for each type node. -/
private def resolveType {n} (self : Typ n) : Rec Typ := λ fuel =>
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .TLit => .yield .TLit
    | .TFn tIn tOut =>
      (resolveType tIn fuel).flatMap (λ input =>
        (resolveType tOut fuel).map (λ output => .TFn input output))

/-- Resolve a term using the caller's type bindings. Every recursive resolution consumes one unit of fuel. -/
def infer {n} (self : Trm n)
    (bindings : Nat → Option ((context : Nat) × Typ context)) : RecOpt Typ := λ fuel =>
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val (.lit _) => .yield (some .TLit)
    | .val (.fn tIn body) =>
      (resolveType tIn fuel).flatMap (λ input =>
        (infer (body.apply .only)
          (λ index => if index = n + 2 then some ⟨n, tIn⟩
            else if index = n + 1 then none else bindings index) fuel).map
          (λ output => output.map (λ tOut => .TFn input tOut)))
    | .ref _ under =>
      match bindings under.sourceIndex with
      | some ⟨_, typ⟩ => (resolveType typ fuel).map some
      | none => .yield none
    | .apply fn arg =>
      match infer fn bindings fuel, infer arg bindings fuel with
      | .yield (some (.TFn tIn tOut)), .yield (some argTyp) =>
        if argTyp ≤ tIn then .yield (some tOut) else .yield none
      | .yield _, .yield _ => .yield none
      | _, _ => .outOfFuel

private theorem resolveTypeMonotone {n} (typ : Typ n) : (resolveType typ).Monotone := by
  intro less more result hFuel hInfer
  induction less generalizing n typ more result with
  | zero => simp [resolveType] at hInfer
  | succ fuel ih =>
    cases more with
    | zero => cases hFuel
    | succ more =>
      have hFuelTail := Nat.le_of_succ_le_succ hFuel
      cases typ <;> simp only [resolveType.eq_2, resolveType.eq_3,
        Rec.Outcome.flatMap, Rec.Outcome.map] at hInfer ⊢
      all_goals
        repeat split at hInfer
        all_goals simp_all
      all_goals
        rename_i tIn tOut _ input hIn _ output hOut
        simpa [ih tIn more input hFuelTail hIn, ih tOut more output hFuelTail hOut] using hInfer

/-- Every completed inference result, including rejection, is preserved when fuel increases. -/
theorem termInferMonotone {n} (trm : Trm n)
    (bindings : Nat → Option ((context : Nat) × Typ context)) :
    (infer trm bindings).Monotone := by
  intro less more result hFuel hInfer
  induction less generalizing n trm bindings more result with
  | zero => simp [infer] at hInfer
  | succ fuel ih =>
    cases more with
    | zero => cases hFuel
    | succ more =>
      have hFuelTail := Nat.le_of_succ_le_succ hFuel
      have hTypes {n} (typ : Typ n) (result) := resolveTypeMonotone typ fuel more result hFuelTail
      cases trm <;> try cases ‹Val n›
      all_goals
        simp only [infer.eq_2, infer.eq_3, infer.eq_4, infer.eq_5,
          Rec.Outcome.flatMap, Rec.Outcome.map] at hInfer ⊢
        repeat split at hInfer
        all_goals simp_all
      all_goals
        have hTypeTop := hTypes _ _ (by assumption)
        simp_all

/-- Value inference monotonicity follows from term inference monotonicity. -/
theorem valueInferMonotone {n} (value : Val n)
    (bindings : Nat → Option ((context : Nat) × Typ context)) :
    (infer value.asTrm bindings).Monotone :=
  termInferMonotone value.asTrm bindings

end AST
end Lp2lc.Active.STLC
