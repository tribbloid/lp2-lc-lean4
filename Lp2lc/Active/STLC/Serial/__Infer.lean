import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util
namespace AST

/-- Resolve syntax using the caller's type bindings. Every recursive resolution consumes one unit of fuel. -/
def infer {n l} (self : AST n l)
    (bindings : Nat → Option ((context : Nat) × Typ context)) : RecOpt Typ := λ fuel =>
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .TLit
    | .lit _ => .yield (some .TLit)
    | .TFn tIn tOut =>
      (infer tIn bindings fuel).flatMap (λ input =>
        (infer tOut bindings fuel).map (λ output => .TFn <$> input <*> output))
    | .fn tIn body =>
      (infer tIn bindings fuel).flatMap (λ input =>
        (infer (body.apply .only)
          (λ index => if index = n + 2 then some ⟨n, tIn⟩
            else if index = n + 1 then none else bindings index) fuel).map
          (λ output => .TFn <$> input <*> output))
    | .val value => infer value bindings fuel
    | .ref (lower := lower) _ _ =>
      match bindings lower with
      | some ⟨_, typ⟩ => infer typ bindings fuel
      | none => .yield none
    | .apply fn arg =>
      match infer fn bindings fuel, infer arg bindings fuel with
      | .yield (some (.TFn tIn tOut)), .yield (some argTyp) =>
        if argTyp ≤ tIn then .yield (some tOut) else .yield none
      | .yield _, .yield _ => .yield none
      | _, _ => .outOfFuel

/-- Inference that succeeds with smaller fuel succeeds with the same type at larger fuel. -/
theorem termInferMonotone {n l} (trm : AST n l)
    (bindings : Nat → Option ((context : Nat) × Typ context)) :
    (infer trm bindings).Monotone := by
  intro less more result hFuel hInfer
  induction less generalizing n l trm bindings more result with
  | zero => simp [infer] at hInfer
  | succ fuel ih =>
    cases more with
    | zero => cases hFuel
    | succ more =>
      have hFuelTail := Nat.le_of_succ_le_succ hFuel
      cases trm <;>
        simp only [infer.eq_2, infer.eq_3, infer.eq_4, infer.eq_5,
          infer.eq_6, infer.eq_7, infer.eq_8, Rec.Outcome.flatMap, Rec.Outcome.map] at hInfer ⊢
      all_goals
        repeat split at hInfer
        all_goals simp_all

/-- Value inference monotonicity follows from term inference monotonicity. -/
theorem valueInferMonotone {n} (value : Val n)
    (bindings : Nat → Option ((context : Nat) × Typ context)) :
    (infer value.asTrm bindings).Monotone :=
  termInferMonotone value.asTrm bindings

end AST
end Lp2lc.Active.STLC
