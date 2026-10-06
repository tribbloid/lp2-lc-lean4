import «Lp2lc».Active.STLC.Serial.Eval

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util
namespace AST

abbrev ValOrTyp := ExeValue ⊕ Typ -- Inference at a breakpoint accepts runtime values or types.

abbrev BuildBindings := Nat → Option ValOrTyp -- append-only

/-- Convert a known type to the result context, consuming fuel for each type node. -/
def resolveType {n} (self : Typ n) : Rec Typ := λ fuel =>
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .TLit => .yield .TLit
    | .TFn tIn tOut =>
      (resolveType tIn fuel).flatMap (λ input =>
        (resolveType tOut fuel).map (.TFn input))

/-- Infer using runtime values or hypothetical types, resolving runtime values in their captured environments. -/
def inferInternal {n} (self : Trm n) (bindings : BuildBindings) : RecOpt Typ := λ fuel =>
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val (.lit _) => .yield (some .TLit)
    | .val (.fn tIn body) =>
      (resolveType tIn fuel).flatMap (λ input =>
        (inferInternal (body.apply .only)
          (λ index => if index = n + 1 then some (.inr input) else bindings index) fuel).map
          (Option.map (.TFn input)))
    | .ref _ under =>
      match bindings under.sourceIndex with
      | some (.inl (.mk _ value captured)) =>
        inferInternal value.asTrm (λ index => (captured index).map .inl) fuel
      | some (.inr typ) => .yield (some typ)
      | none => .yield none
    | .apply fn arg =>
      match inferInternal fn bindings fuel, inferInternal arg bindings fuel with
      | .yield (some (.TFn tIn tOut)), .yield (some argTyp) =>
        .yield (if argTyp ≤ tIn then some tOut else none)
      | .yield _, .yield _ => .yield none
      | _, _ => .outOfFuel

/-- Infer with no external runtime bindings. -/
def infer {n} (self : Trm n) : RecOpt Typ :=
  self.inferInternal (λ _ => none)

variable {n : Nat}

namespace Monotone

theorem resolveType (typ : Typ n) : (resolveType typ).Monotone := by
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
        simp_all [ih tIn more input hFuelTail hIn, ih tOut more output hFuelTail hOut]

/-- Every completed inference result, including rejection, is preserved when fuel increases. -/
theorem termInfer (trm : Trm n)
    (bindings : BuildBindings) :
    (inferInternal trm bindings).Monotone := by
  intro less more result hFuel hInfer
  induction less generalizing n trm bindings more result with
  | zero => simp [inferInternal] at hInfer
  | succ fuel ih =>
    cases more with
    | zero => cases hFuel
    | succ more =>
      have hFuelTail := Nat.le_of_succ_le_succ hFuel
      cases trm <;> try cases ‹Val n›
      all_goals
        simp only [inferInternal.eq_2, inferInternal.eq_3, inferInternal.eq_4, inferInternal.eq_5,
          Rec.Outcome.flatMap, Rec.Outcome.map] at hInfer ⊢
        repeat split at hInfer
        all_goals simp_all
      all_goals simp_all [resolveType _ fuel more _ hFuelTail (by assumption)]

/-- Value inference monotonicity follows from term inference monotonicity. -/
theorem valueInfer (value : Val n)
    (bindings : BuildBindings) :
    (inferInternal value.asTrm bindings).Monotone :=
  termInfer value.asTrm bindings

end Monotone

end AST
end Lp2lc.Active.STLC
