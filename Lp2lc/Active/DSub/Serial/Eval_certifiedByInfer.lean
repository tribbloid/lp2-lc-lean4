import «Lp2lc».Active.DSub.Serial.Infer

namespace Lp2lc.Active.DSub.AST

open Lp2lc.Active.Util

namespace CertifiedByInfer

abbrev ConditionalVal (condition : CompilerTyp → Prop) :=
  {value : ExeVal // (value.value.asTrm.infer value.captured).isDecidable condition}

private def acceptsType (actual expected : CompilerTyp) : Prop :=
  ∃ fuel, actual.subtype expected .empty fuel = .yield true

/-- A returned value whose independently inferred type passes the existing subtype check. -/
abbrev CertifiedVal (typ : CompilerTyp) :=
  ConditionalVal (λ actual => acceptsType actual typ)

/-- Fuel-bounded certified evaluation may still exhaust its fuel. -/
abbrev Result (typ : CompilerTyp) := Rec (CertifiedVal typ)

private def preservesType (source target : RecOpt CompilerTyp) : Prop :=
  ∀ {fuel typ}, source fuel = .yield (some typ) →
    target.isDecidable (λ actual => acceptsType actual typ)

/-- Each returned value preserves every successful inference of its source term.
Recursive resolution consumes fuel; primitive results are checked against their dependent annotations.
Rejection, corruption, and unsuccessful checks report `outOfFuel`.
A terminating accepted term may still lack a certificate at every fuel budget. -/
private def evalInternal {n} (self : Trm n) (bindings : ExeBindings) :
    Rec {value : ExeVal //
      preservesType (self.infer bindings) (value.value.asTrm.infer value.captured)} := λ budget =>
  match budget with
  | 0 => .outOfFuel
  | fuel + 1 =>
    let run {m} (trm : Trm m) (captured : ExeBindings) : Rec.Outcome ExeVal :=
      (evalInternal trm captured fuel).map Subtype.val
    let result : Rec.Outcome ExeVal :=
      match self with
      | .val (.ref _ under) =>
        match bindings under.sourceIndex.down with
        | none => .outOfFuel
        | some value =>
          match value.value with
          | .ref _ _ => run value.value.asTrm value.captured
          | _ => .yield value
      | .val value => .yield ⟨n, value, bindings⟩
      | .apply fn arg =>
        match run fn bindings, run arg bindings with
        | .yield ⟨context, .fn _ body, captured⟩, .yield value =>
          run (body.apply .only) (captured.set (context + 1) value)
        | .yield ⟨context, .fnPrimitive output op, captured⟩, .yield argument =>
          match argument.value with
          | .lit repr =>
            let value : Val context := op repr
            -- An exact member declaration resolves the result annotation using this literal argument.
            match infer (.val (.typeDef (output.apply .only))) (captured.set (context + 1) argument) fuel,
                value.asTrm.infer captured fuel with
            | .yield (some ⟨index, .TMember _ expected, typeCaptures⟩), .yield (some actual) =>
              (actual.subtype ⟨index, expected, typeCaptures⟩ .empty fuel).flatMap (λ accepted =>
                if accepted then run value.asTrm captured else .outOfFuel)
            | _, _ => .outOfFuel
          | _ => .outOfFuel
        | _, _ => .outOfFuel
    result.flatMap (λ value =>
      match _hSource : self.infer bindings budget,
          _hValue : value.value.asTrm.infer value.captured budget with
      | .yield (some expected), .yield (some actual) =>
        match _hSubtype : actual.subtype expected .empty budget with
        | .yield true => .yield ⟨value, by
            intro inferFuel typ hInfer
            have hMono := Monotone.termInfer self bindings
            have hSame := (hMono budget (max budget inferFuel) _ (Nat.le_max_left _ _) _hSource).symm.trans
              (hMono inferFuel (max budget inferFuel) _ (Nat.le_max_right _ _) hInfer)
            cases Rec.Outcome.yield.inj hSame
            exact ⟨budget, by rw [_hValue]; exact ⟨budget, _hSubtype⟩⟩⟩
        | _ => .outOfFuel
      | _, _ => .outOfFuel)

namespace Monotone

/-- Completed evaluation results are preserved when fuel increases. -/
private theorem termEval {n} (trm : Trm n) (bindings : ExeBindings) :
    (evalInternal trm bindings).Monotone := by
  intro less more result hFuel h
  induction less generalizing n trm bindings more result with
  | zero => cases h
  | succ fuel ih =>
    cases more with
    | zero => exact False.elim (Nat.not_succ_le_zero _ hFuel)
    | succ more =>
      replace hFuel := Nat.le_of_succ_le_succ hFuel
      have hRun {m} (self : Trm m) entries value :
          (evalInternal self entries fuel).map Subtype.val = .yield value →
          (evalInternal self entries more).map Subtype.val = .yield value := by
        cases hResult : evalInternal self entries fuel with
        | outOfFuel => simp [Rec.Outcome.map]
        | yield result =>
          intro h
          rw [ih self entries more result hFuel hResult]
          exact h
      have hInfer := @AST.Monotone.termInfer
      have hSubtype := CompilerTyp.Monotone.subtype
      simp only [Rec.Monotone] at hInfer hSubtype
      cases trm <;> try cases ‹Val n›
      all_goals simp only [evalInternal, Rec.Outcome.flatMap] at h ⊢
      all_goals repeat' split at h
      all_goals try grind (splits := 0)
      all_goals rename_i hRaw expected actual hSource hValue hSubtypeCheck
      all_goals repeat' split at hRaw
      all_goals grind (splits := 1)

end Monotone

end CertifiedByInfer

open CertifiedByInfer

/-- Evaluate an independently inferred term and certify its returned value at the inferred type. -/
def eval_certified {n} (self : Trm n) (bindings : ExeBindings := .empty)
    {inferFuel : Nat} {typ : CompilerTyp}
    (hInfer : self.infer bindings inferFuel = .yield (some typ)) : Result typ := λ fuel =>
  (evalInternal self bindings fuel).map (λ result => ⟨result.val, result.property hInfer⟩)

end Lp2lc.Active.DSub.AST
