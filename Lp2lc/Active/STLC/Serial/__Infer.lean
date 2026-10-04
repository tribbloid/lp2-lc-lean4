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
    | .ref (lower := lower) _ _ =>
      match bindings lower with
      | some ⟨_, typ⟩ => (resolveType typ fuel).map some
      | none => .yield none
    | .apply fn arg =>
      match infer fn bindings fuel, infer arg bindings fuel with
      | .yield (some (.TFn tIn tOut)), .yield (some argTyp) =>
        if argTyp ≤ tIn then .yield (some tOut) else .yield none
      | .yield _, .yield _ => .yield none
      | _, _ => .outOfFuel

/-- Inference that succeeds with smaller fuel succeeds with the same type at larger fuel. -/
theorem termInferMonotone {n} (trm : Trm n)
    (bindings : Nat → Option ((context : Nat) × Typ context)) :
    (infer trm bindings).Monotone := by sorry

/-- Value inference monotonicity follows from term inference monotonicity. -/
theorem valueInferMonotone {n} (value : Val n)
    (bindings : Nat → Option ((context : Nat) × Typ context)) :
    (infer value.asTrm bindings).Monotone :=
  termInferMonotone value.asTrm bindings

end AST
end Lp2lc.Active.STLC
