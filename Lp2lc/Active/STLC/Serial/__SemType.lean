import «Lp2lc».Active.STLC.Serial.Eval
import «Lp2lc».Active.STLC.Serial.Infra

namespace Lp2lc.Active.STLC.AST.Semantic

open Lp2lc.Active.Util

/-- Fuel-bounded typing with runtime values or hypothetical types.

Application quantifies over its domain; no principal type is selected.
-/
def check {n} (self : Trm n) (typ : Typ)
    (bindings : CompilerBindings := .empty) : Rec Prop
  | 0 => .yield False
  | fuel + 1 =>
    .yield (match self, typ with
      | .val (.lit _), .TLit => True
      | .val (.lit _), .TFn _ _
      | .val (.fn _ _), .TLit => False
      | .val (.fn annotation body), .TFn input output =>
        resolveType annotation = input ∧
          (check (body.apply .only) output
            (bindings.set (n + 1) ⟨n, .inr annotation, bindings⟩) fuel).getOrElse False
      | .ref _ under, _ =>
        match bindings under.sourceIndex.down with
        | some ⟨_, .inl value, captured⟩ => (check value.asTrm typ captured fuel).getOrElse False
        | some ⟨_, .inr bound, _⟩ => resolveType bound = typ
        | none => False
      | .apply fn arg, _ =>
        ∃ input, (check fn (.TFn input typ) bindings fuel).getOrElse False ∧
          (check arg input bindings fuel).getOrElse False)

def semType {n} (self : Trm n) (bindings : CompilerBindings) (fuel : Nat) (typ: Typ) : Prop :=
  (check self typ bindings fuel).getOrElse False

namespace Monotone

/-- Typing evidence remains valid when the fuel bound increases. -/
theorem termCheck {n} (trm : Trm n) (bindings : CompilerBindings)
    {less more : Nat} {typ : Typ} (hFuel : less ≤ more)
    (hType : semType trm bindings less typ) : semType trm bindings more typ := by
  induction less generalizing n trm bindings more typ with
  | zero => simp [semType, check, Rec.Outcome.getOrElse] at hType
  | succ fuel ih =>
    cases more <;> try (exact False.elim (Nat.not_succ_le_zero _ hFuel))
    replace hFuel := Nat.le_of_succ_le_succ hFuel
    cases trm with
    | val value =>
      cases value with
      | lit repr => cases typ <;> exact hType
      | fn annotation body =>
        cases typ <;> simp only [semType, check, Rec.Outcome.getOrElse] at hType ⊢
        exact ⟨hType.1, ih _ _ hFuel hType.2⟩
    | ref carrier under =>
      simp only [semType, check, Rec.Outcome.getOrElse] at hType ⊢
      cases hEntry : bindings under.sourceIndex.down <;>
        (try cases ‹CompilerTyp›) <;> (try cases ‹Val _ ⊕ Typ _›)
      all_goals simp only [hEntry] at hType ⊢
      all_goals first | exact hType | exact ih _ _ hFuel hType
    | apply fn arg =>
      obtain ⟨input, hFn, hArg⟩ := hType
      exact ⟨input, ih _ _ hFuel hFn, ih _ _ hFuel hArg⟩

end Monotone

end Lp2lc.Active.STLC.AST.Semantic
