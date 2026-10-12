import «Lp2lc».Active.STLC.Serial.Eval
import «Lp2lc».Active.STLC.Serial.Infra

namespace Lp2lc.Active.STLC.AST.Semantic

open Lp2lc.Active.Util

/-- Erase the context index of an annotation without consuming typing fuel. -/
private def closeType {n} (self : Typ n) : Typ :=
  match self with
  | .TLit => .TLit
  | .TFn input output => .TFn (closeType input) (closeType output)

/-- Fuel-bounded typing with runtime values or hypothetical types.

Application quantifies over its domain; no principal type is selected.
-/
def checkInternal {n} (self : Trm n) (typ : Typ)
    (bindings : CompilerBindings := .empty) : Rec Prop := λ fuel =>
  match fuel with
  | 0 => .yield False
  | fuel + 1 =>
    .yield (match self with
      | .val (.lit _) => .TLit ≤ typ
      | .val (.fn annotation body) =>
        match typ with
        | .TLit => False
        | .TFn input output =>
          closeType annotation = input ∧
            (checkInternal (body.apply .only) output
              (bindings.set (n + 1) (.inr input)) fuel).getOrElse False
      | .ref _ under =>
        match bindings under.sourceIndex.down with
        | some (.inl (.mk _ value captured)) =>
          (checkInternal value.asTrm typ (captured.map .inl) fuel).getOrElse False
        | some (.inr bound) => bound ≤ typ
        | none => False
      | .apply fn arg =>
        ∃ input, (checkInternal fn (.TFn input typ) bindings fuel).getOrElse False ∧
          (checkInternal arg input bindings fuel).getOrElse False)

def check {n} (self : Trm n) (typ : Typ)
    (bindings : ExeBindings := .empty) : Rec Prop :=
  checkInternal self typ (bindings.map .inl)

def semType {n} (self : Trm n) (bindings : CompilerBindings) (fuel : Nat) (typ: Typ) : Prop :=
  (checkInternal self typ bindings fuel).getOrElse False

namespace Monotone

/-- Typing evidence remains valid when the fuel bound increases. -/
theorem termCheck {n} (trm : Trm n) (bindings : CompilerBindings)
    {less more : Nat} {typ : Typ} (hFuel : less ≤ more)
    (hType : semType trm bindings less typ) : semType trm bindings more typ := by
  induction less generalizing n trm bindings more typ with
  | zero => simp [semType, checkInternal, Rec.Outcome.getOrElse] at hType
  | succ fuel ih =>
    cases more <;> try (exact False.elim (Nat.not_succ_le_zero _ hFuel))
    replace hFuel := Nat.le_of_succ_le_succ hFuel
    cases trm with
    | val value =>
      cases value with
      | lit repr => exact hType
      | fn annotation body =>
        cases typ <;> simp only [semType, checkInternal, Rec.Outcome.getOrElse] at hType ⊢
        exact ⟨hType.1, ih _ _ hFuel hType.2⟩
    | ref carrier under =>
      simp only [semType, checkInternal, Rec.Outcome.getOrElse] at hType ⊢
      cases hEntry : bindings under.sourceIndex.down <;>
        (try cases ‹ValOrTyp›) <;> (try cases ‹ExeValue›)
      all_goals simp only [hEntry] at hType ⊢
      all_goals first | exact hType | exact ih _ _ hFuel hType
    | apply fn arg =>
      obtain ⟨input, hFn, hArg⟩ := hType
      exact ⟨input, ih _ _ hFuel hFn, ih _ _ hFuel hArg⟩

end Monotone

end Lp2lc.Active.STLC.AST.Semantic
