import Batteries.Tactic.OpenPrivate

import «Lp2lc».Active.DSub.Serial.Infer

namespace Lp2lc.Active.DSub.CompilerTyp

open Lp2lc.Active.Util

-- Certification uses the existing private subtype implementation.
open private CompilerTyp.combine memberBounds selectionBounds from Lp2lc.Active.DSub.Serial.Infer

namespace Monotone

private theorem combine {left right left' right' : Rec.Outcome Bool} {result : Bool}
    (shortCircuit : Bool)
    (hLeft : ∀ value, left = .yield value → left' = .yield value)
    (hRight : ∀ value, right = .yield value → right' = .yield value)
    (h : CompilerTyp.combine shortCircuit left right = .yield result) :
    CompilerTyp.combine shortCircuit left' right' = .yield result := by
  cases left <;> cases right <;> cases shortCircuit <;> simp_all [CompilerTyp.combine]
  all_goals split at h <;> simp_all
  all_goals cases left' <;> cases right' <;> simp_all

private theorem bounds (less more : Nat) (hFuel : less ≤ more) :
    (∀ self context result, memberBounds self context less = .yield result →
      memberBounds self context more = .yield result) ∧
    (∀ {n} (value : Pure n) captured context result, selectionBounds value captured context less = .yield result →
      selectionBounds value captured context more = .yield result) := by
  induction less generalizing more with
  | zero => constructor <;> intros <;> contradiction
  | succ fuel ih =>
    cases more with
    | zero => exact False.elim (Nat.not_succ_le_zero _ hFuel)
    | succ more =>
      obtain ⟨hMember, hSelection⟩ := ih more (Nat.le_of_succ_le_succ hFuel)
      constructor
      · rintro ⟨n, typ, captured⟩ context result h
        cases typ
        all_goals simp only [memberBounds, Rec.Outcome.flatMap] at h ⊢
        all_goals repeat split at h
        all_goals simp_all <;> subst_vars <;> rfl
      · intro n value captured context result h
        cases value <;> try cases ‹Val n›
        all_goals simp only [selectionBounds] at h ⊢
        all_goals repeat split at h
        all_goals simp_all

/-- Completed subtype checks retain their result when fuel increases. -/
private theorem subtype (self upper : CompilerTyp) (context : NatBindings CompilerTyp) :
    (self.subtype upper context).Monotone := by
  intro less more result hFuel h
  induction less generalizing self upper context more result with
  | zero => cases h
  | succ fuel ih =>
    cases more with
    | zero => exact False.elim (Nat.not_succ_le_zero _ hFuel)
    | succ more =>
      replace hFuel := Nat.le_of_succ_le_succ hFuel
      obtain ⟨_, hSelection⟩ := bounds fuel more hFuel
      simp only [CompilerTyp.subtype.eq_2] at h ⊢
      repeat' (split at h <;> try simp_all only [Bool.false_eq_true, ite_true, ite_false])
      all_goals apply combine _ ?_ ?_ h
      all_goals intro value hBranch
      all_goals try exact ih _ _ _ more value hFuel hBranch
      all_goals try simp only [Rec.Outcome.flatMap] at hBranch ⊢
      all_goals repeat split at hBranch
      all_goals simp_all [-Bool.forall_bool]

end Monotone

end Lp2lc.Active.DSub.CompilerTyp

namespace Lp2lc.Active.DSub.AST

open Lp2lc.Active.Util

-- Certification uses the existing private inference implementation.
open private AST.quoteType AST.quoteType.visit AST.functionType resolveType andThen AST.bind
  from Lp2lc.Active.DSub.Serial.Infer

namespace Monotone

/-- Completed quotation results retain their syntax when fuel increases. -/
private theorem quoteType (self : CompilerTyp) (imports : Option ExeBindings)
    (context : NatBindings CompilerTyp) (target : Nat) (names : Nat → Nat)
    (targetCaptures : NatBindings CompilerTyp) :
    (AST.quoteType self imports context target names targetCaptures).Monotone := by
  intro less more result hFuel h
  induction less generalizing self imports context target names targetCaptures more result with
  | zero => cases h
  | succ fuel ih =>
    cases more with
    | zero => exact False.elim (Nat.not_succ_le_zero _ hFuel)
    | succ more =>
      replace hFuel := Nat.le_of_succ_le_succ hFuel
      obtain ⟨hMember, _⟩ := CompilerTyp.Monotone.bounds fuel more hFuel
      have hSubtype (self upper : CompilerTyp) (context : NatBindings CompilerTyp) (value : Bool) :=
        CompilerTyp.Monotone.subtype self upper context fuel more value hFuel
      have hCheck (lower upper : CompilerTyp) (context : NatBindings CompilerTyp) (value : Bool) :=
        CompilerTyp.Monotone.combine (result := value) false (hSubtype lower upper context) (hSubtype upper lower context)
      let rec visit {P l} (node : Pre.AST P l) (get : ∀ index, P.I.getTRef index)
          (encoding : P.I = .Serial) (captured context : NatBindings CompilerTyp)
          (target : Nat) (names : Nat → Nat) (targetCaptures : NatBindings CompilerTyp) (result) :
          AST.quoteType.visit imports fuel (λ a b c d e f => AST.quoteType a b c d e f fuel)
              node get encoding captured context target names targetCaptures = .yield result →
          AST.quoteType.visit imports more (λ a b c d e f => AST.quoteType a b c d e f more)
              node get encoding captured context target names targetCaptures = .yield result := by
        match node with
        | .TMember lower upper =>
          have hLower := visit lower get encoding
          have hUpper := visit upper get encoding
          simp only [AST.quoteType.visit, andThen, Rec.Outcome.map, Rec.Outcome.flatMap]
          intro h
          repeat' split at h
          all_goals simp_all [-Bool.forall_bool] <;> subst_vars <;> simp_all
        | .TFn input (AST.bind output) =>
          have hInput := visit input get encoding
          have hOutput := visit (output (get P.Next.index)) get encoding
          unfold AST.quoteType.visit
          simp only [andThen, Rec.Outcome.map, Rec.Outcome.flatMap]
          intro h
          repeat' split at h
          all_goals simp_all [AST.bind, Pre.Binder.mk, -Bool.forall_bool] <;> subst_vars <;> simp_all
        | .TSel (.val (.typeDef typ)) =>
          exact visit typ get encoding captured context target names targetCaptures result
        | .TSel (.val (.lit _))
        | .TSel (.val (.fn _ _))
        | .TSel (.val (.fnPrimitive _ _)) => exact id
        | .TSel (.ref _ _) =>
          intro h
          simp only [AST.quoteType.visit, andThen, Rec.Outcome.flatMap] at h ⊢
          repeat' split at h
          all_goals try simp_all [-Bool.forall_bool]
          all_goals exact ih _ _ _ _ _ _ more _ hFuel h
        | .TTop
        | .TBot
        | .TLit
        | .lit _
        | .fn _ _
        | .fnPrimitive _ _
        | .typeDef _
        | .val _
        | .pure _
        | .ref _ _
        | .apply _ _ => exact id
      termination_by structural node
      exact visit self.value (λ _ => .only) rfl self.captured context target names targetCaptures result h

private theorem functionType (self : CompilerTyp) (context : NatBindings CompilerTyp) :
    (AST.functionType self context).Monotone := by
  intro less more result hFuel h
  induction less generalizing self context more result with
  | zero => cases h
  | succ fuel ih =>
    cases more with
    | zero => exact False.elim (Nat.not_succ_le_zero _ hFuel)
    | succ more =>
      replace hFuel := Nat.le_of_succ_le_succ hFuel
      obtain ⟨_, hSelection⟩ := CompilerTyp.Monotone.bounds fuel more hFuel
      rcases self with ⟨n, typ, captured⟩
      cases typ
      all_goals simp only [AST.functionType, andThen, Rec.Outcome.flatMap] at h ⊢
      all_goals repeat' split at h
      all_goals simp_all <;> subst_vars <;> rfl

/-- Every completed inference result, including rejection, is preserved when fuel increases. -/
private theorem termInfer {n} (trm : Trm n) (bindings : CompilerBindings) :
    (infer trm bindings).Monotone := by
  intro less more result hFuel h
  induction less generalizing n trm bindings more result with
  | zero => cases h
  | succ fuel ih =>
    cases more with
    | zero => exact False.elim (Nat.not_succ_le_zero _ hFuel)
    | succ more =>
      replace hFuel := Nat.le_of_succ_le_succ hFuel
      have hQuote (self imports context target names captures result) :=
        quoteType self imports context target names captures (fuel + 1) (more + 1) result (Nat.succ_le_succ hFuel)
      have hFunction (self context result) := functionType self context fuel more result hFuel
      have hSubtype (self upper context result) := CompilerTyp.Monotone.subtype self upper context fuel more result hFuel
      cases trm <;> try cases ‹Pure n› <;> try cases ‹Val n›
      all_goals simp only [infer, resolveType, andThen, Rec.Outcome.flatMap, Rec.Outcome.map] at h ⊢
      all_goals repeat' split at h
      all_goals try simp_all [-Bool.forall_bool]
      all_goals repeat' (split at * <;> try simp_all [-Bool.forall_bool])
      all_goals subst_vars <;> first | contradiction | rfl

end Monotone

namespace CertifiedByInfer

private def acceptsType (actual expected : CompilerTyp) : Prop :=
  ∃ fuel, actual.subtype expected .empty fuel = .yield true

/-- A returned value whose independently inferred type passes the existing subtype check. -/
abbrev CertifiedVal (typ : CompilerTyp) :=
  {value : ExeVal // (value.value.asTrm.infer value.captured).isDecidable (λ actual => acceptsType actual typ)}

/-- Certified evaluation preserves runtime corruption and may exhaust its fuel. -/
abbrev Result (typ : CompilerTyp) := Rec (Return (CertifiedVal typ))

private def preservesType (source target : RecOpt CompilerTyp) : Prop :=
  ∀ {fuel typ}, source fuel = .yield (some typ) →
    target.isDecidable (λ actual => acceptsType actual typ)

/-- Each returned value preserves every successful inference of its source term.
Recursive resolution consumes fuel; primitive results are checked against their dependent annotations.
Conclusive runtime contract failures report `corrupted`; incomplete checks report `outOfFuel`. -/
private def evalInternal {n} (self : Trm n) (bindings : ExeBindings) (validationFuel : Nat) :
    Rec (Return {value : ExeVal //
      preservesType (self.infer bindings) (value.value.asTrm.infer value.captured)}) := λ budget =>
  match budget with
  | 0 => .outOfFuel
  | fuel + 1 =>
    let validation := max validationFuel budget
    let run {m} (trm : Trm m) (captured : ExeBindings) : Rec.Outcome (Return ExeVal) :=
      (evalInternal trm captured validationFuel fuel).map (·.map Subtype.val)
    let result : Rec.Outcome (Return ExeVal) :=
      match self with
      | .pure (.ref _ under) =>
        match bindings under.sourceIndex.down with
        | none => .yield .corrupted
        | some value => .yield (.some value)
      | .pure (.val value) => .yield (.some ⟨n, value, bindings⟩)
      | .apply fn arg =>
        match run fn bindings, run arg bindings with
        | .yield (.some ⟨context, .fn _ body, captured⟩), .yield (.some value) =>
          run (body.apply .only) (captured.set (context + 1) value)
        | .yield (.some ⟨context, .fnPrimitive output op, captured⟩), .yield (.some argument) =>
          match argument.value with
          | .lit repr =>
            let value : Val context := op repr
            -- An exact member declaration resolves the result annotation using this literal argument.
            match infer (.pure (.val (.typeDef (output.apply .only)))) (captured.set (context + 1) argument) validation,
                value.asTrm.infer captured validation with
            | .yield (some ⟨index, .TMember _ expected, typeCaptures⟩), .yield (some actual) =>
              (actual.subtype ⟨index, expected, typeCaptures⟩ .empty validation).flatMap (λ accepted =>
                if accepted then run value.asTrm captured else .yield .corrupted)
            | .yield _, .yield _ => .yield .corrupted
            | _, _ => .outOfFuel
          | _ => .yield .corrupted
        | .yield _, .yield _ => .yield .corrupted
        | _, _ => .outOfFuel
    match result with
    | .outOfFuel => .outOfFuel
    | .yield .corrupted => .yield .corrupted
    | .yield (.some value) =>
      match _hSource : self.infer bindings validation,
          _hValue : value.value.asTrm.infer value.captured validation with
      | .yield (some expected), .yield (some actual) =>
        match _hSubtype : actual.subtype expected .empty validation with
        | .yield true => .yield (.some ⟨value, by
            intro inferFuel typ hInfer
            have hMono := Monotone.termInfer self bindings
            have hSame := (hMono validation (max validation inferFuel) _ (Nat.le_max_left _ _) _hSource).symm.trans
              (hMono inferFuel (max validation inferFuel) _ (Nat.le_max_right _ _) hInfer)
            cases Rec.Outcome.yield.inj hSame
            exact ⟨validation, by rw [_hValue]; exact ⟨validation, _hSubtype⟩⟩⟩)
        | .yield false => .yield .corrupted
        | .outOfFuel => .outOfFuel
      | .yield _, .yield _ => .yield .corrupted
      | _, _ => .outOfFuel

end CertifiedByInfer

/-- Evaluate an independently inferred term and certify its returned value at the inferred type. -/
def eval_certified {n} (self : Trm n) (bindings : ExeBindings := .empty)
    {inferFuel : Nat} {typ : CompilerTyp}
    (hInfer : self.infer bindings inferFuel = .yield (some typ)) : CertifiedByInfer.Result typ := λ fuel =>
  (CertifiedByInfer.evalInternal self bindings inferFuel fuel).map (·.map (λ result => ⟨result.val, result.property hInfer⟩))

end Lp2lc.Active.DSub.AST
