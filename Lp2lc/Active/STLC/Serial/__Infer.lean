import «Lp2lc».Active.STLC.Serial.Eval
namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util
namespace AST

abbrev ValOrTyp := ExeValue ⊕ Typ -- Inference at a breakpoint accepts runtime values or types.

abbrev BuildBindings := Bindings ValOrTyp -- append-only

/-- Convert `Typ n` to `Typ 0`, preserving its structure without consuming inference fuel. -/
def resolveType {n} (self : Typ n) : Typ :=
  match self with
  | .TLit => .TLit
  | .TFn tIn tOut => .TFn (resolveType tIn) (resolveType tOut)

/-- Infer using runtime values or hypothetical types, resolving runtime values in their captured environments. -/
def inferInternal {n} (self : Trm n) (bindings : BuildBindings) : RecOpt Typ := λ fuel =>
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val (.lit _) => .yield (some .TLit)
    | .val (.fn tIn body) =>
      let input := resolveType tIn
      (inferInternal (body.apply .only)
        (bindings.set (n + 1) (.inr input)) fuel).map
        (Option.map (.TFn input))
    | .ref _ under =>
      match bindings under.sourceIndex with
      | some (.inl (.mk _ value captured)) =>
        inferInternal value.asTrm (captured.map .inl) fuel
      | some (.inr typ) => .yield (some typ)
      | none => .yield none
    | .apply fn arg =>
      match inferInternal fn bindings fuel, inferInternal arg bindings fuel with
      | .yield (some (.TFn tIn tOut)), .yield (some argTyp) =>
        .yield (if argTyp ≤ tIn then some tOut else none)
      | .yield _, .yield _ => .yield none
      | _, _ => .outOfFuel

/-- Infer using runtime values only, resolving each captured value to its type. -/
def infer {n} (self : Trm n) (exeBindings : ExeBindings := .empty) : RecOpt Typ :=
  self.inferInternal (exeBindings.map .inl)

variable {n : Nat}

namespace Monotone

/-- Every completed inference result, including rejection, is preserved when fuel increases. -/
theorem termInfer (trm : Trm n)
    (bindings : BuildBindings) :
    (inferInternal trm bindings).Monotone := by
  intro less more result hFuel hInfer
  induction less generalizing n trm bindings more result with
  | zero => simp [inferInternal] at hInfer
  | succ fuel ih =>
    cases more <;> try (exact False.elim (Nat.not_succ_le_zero _ hFuel))
    replace hFuel := Nat.le_of_succ_le_succ hFuel
    cases trm <;> try cases ‹Val n›
    all_goals
      simp only [inferInternal.eq_2, inferInternal.eq_3, inferInternal.eq_4, inferInternal.eq_5,
        Rec.Outcome.map] at hInfer ⊢
      repeat split at hInfer
      all_goals simp_all

end Monotone

end AST
end Lp2lc.Active.STLC
