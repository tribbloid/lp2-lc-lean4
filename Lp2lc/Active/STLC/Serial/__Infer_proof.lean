import «Lp2lc».Active.STLC.Serial.__Infer

namespace Lp2lc.Active.STLC.Infer_Proof

open Lp2lc.Active.Util

variable {n} (trm : Trm n) (bindings : ExeBindings)

def Safety (typ : Typ) : Prop :=
  (trm.eval bindings).isSemiDecidable (λ result =>
    match result with
    | .mk _ value captured =>
      (value.asTrm.inferInternal (λ index => (captured index).map .inl)).isDecidable (λ inferred => inferred ≤ typ))

/-- A successfully inferred type makes the executable term safe at that type. -/
theorem fundamental (fuel : Nat) (typ : Typ)
    (hInfer : trm.inferInternal (λ index => (bindings index).map .inl) fuel = .yield (some typ)) :
    Safety trm bindings typ := by
  intro evalFuel
  have safe := AST.inferEvalSafety trm bindings fuel typ hInfer evalFuel
  cases result : trm.eval bindings evalFuel with
  | outOfFuel => trivial
  | yield value =>
    cases value with
    | none => simp [result] at safe
    | some value =>
      cases value with
      | mk context value captured =>
        simp only [result] at safe
        obtain ⟨valueFuel, typed⟩ := safe
        exact ⟨valueFuel, by rw [typed]; exact (rfl : typ ≤ typ)⟩

/--
If compilation succeeds, the term must be safe.

TODO: this is the "Paranoid Fundamental theorem": compilation may fail even when term evaluation succeeds.
-/
theorem paranoidFundamental :
    (trm.inferInternal (λ index => (bindings index).map .inl)).ifSucceedMustSatisfy (Safety trm bindings) := by
  intro fuel
  cases result : trm.inferInternal (λ index => (bindings index).map .inl) fuel with
  | outOfFuel => trivial
  | yield value =>
    cases value with
    | none => trivial
    | some typ => exact fundamental trm bindings fuel typ result

end Lp2lc.Active.STLC.Infer_Proof
