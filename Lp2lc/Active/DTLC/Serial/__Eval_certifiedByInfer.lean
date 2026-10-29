import Batteries.Tactic.OpenPrivate

import «Lp2lc».Active.DTLC.Serial.Infer

namespace Lp2lc.Active.DTLC.AST

open Lp2lc.Active.Util

variable {n : Nat}

namespace CertifiedByInfer

/-- A returned value certified at the caller's independently inferred type. -/
abbrev CertifiedVal (typ : Typ) :=
  {value : ExeVal // (value.value.asTrm.infer value.captured).isDecidable (· = typ)}

/-- Corruption is an allowed runtime exit; evaluation may also exhaust its fuel. -/
abbrev Result (typ : Typ) := Rec (Return (CertifiedVal typ))

-- Certification proofs reuse the existing private inference implementation.
open private resolveType typeMatches functionType from Lp2lc.Active.DTLC.Serial.Infer

@[match_pattern] private abbrev bind := @Pre.Binder.mk

variable {m fuel : Nat} {typ : Typ} {entries : CompilerBindings}

/-- Reindexing a type twice has the same result as reindexing it directly. -/
private theorem resolveTypeResolve {P l} (self : Pre.AST P l) (get : ∀ index, P.I.getTRef index)
    (middle target : Nat) :
    resolveType (resolveType self get middle) (λ _ => .only) target = resolveType self get target := by
  match self with
  | .TFn input (bind output) =>
    exact congr (congrArg Pre.AST.TFn (resolveTypeResolve input get middle target))
      (congrArg Pre.Binder.mk (funext (λ _ =>
        resolveTypeResolve (output (get P.Next.index)) get (middle + 1) (target + 1))))
  | .TLit
  | .lit _
  | .fn _ _
  | .fnPrimitive _ _
  | .ref _ _
  | .val _
  | .apply _ _ => rfl
termination_by structural self

/-- A successful structural comparison gives equal types in any common context. -/
private theorem typeMatchesEq {P l m} (self : Pre.AST P l) (other : Typ m)
    (get : ∀ index, P.I.getTRef index) (target : Nat) (h : typeMatches self other get = true) :
    resolveType self get target = resolveType other (λ _ => .only) target := by
  match self with
  | .TFn input (bind output) =>
    cases other with
    | TLit => cases h
    | TFn otherInput otherOutput =>
      cases otherOutput
      rename_i otherOutput
      change typeMatches input otherInput get &&
        typeMatches (output (get P.Next.index)) (otherOutput .only) get = true at h
      have hBoth := Bool.and_eq_true_iff.mp h
      exact congr (congrArg Pre.AST.TFn (typeMatchesEq input otherInput get target hBoth.1))
        (congrArg Pre.Binder.mk (funext (λ _ =>
          typeMatchesEq (output (get P.Next.index)) (otherOutput .only) get (target + 1) hBoth.2)))
  | .TLit => cases other <;> first | rfl | cases h
  | .lit _
  | .fn _ _
  | .fnPrimitive _ _
  | .ref _ _
  | .val _
  | .apply _ _ => cases h
termination_by structural self

/-- The public comparison certifies equality after reindexing to context zero. -/
private theorem sameTypeEq {self : Typ n} {other : Typ m}
    (h : self.sameType other fuel = .yield true) :
    resolveType self (λ _ => .only) = resolveType other (λ _ => .only) := by
  cases fuel with
  | zero => cases h
  | succ fuel => exact typeMatchesEq self other (λ _ => .only) 0 (Rec.Outcome.yield.inj h)

/-- Normalizing the same source type to two contexts preserves structural equality. -/
private theorem typeMatchesResolve {P l} (self : Pre.AST P l) (get : ∀ index, P.I.getTRef index)
    (left right : Nat) :
    typeMatches (resolveType self get left) (resolveType self get right) (λ _ => .only) = true := by
  match self with
  | .TFn input (bind output) =>
    change typeMatches (resolveType input get left) (resolveType input get right) (λ _ => .only) &&
      typeMatches (resolveType (output (get P.Next.index)) get (left + 1))
        (resolveType (output (get P.Next.index)) get (right + 1)) (λ _ => .only) = true
    rw [typeMatchesResolve input get left right,
      typeMatchesResolve (output (get P.Next.index)) get (left + 1) (right + 1)]
    rfl
  | .TLit
  | .lit _
  | .fn _ _
  | .fnPrimitive _ _
  | .ref _ _
  | .val _
  | .apply _ _ => rfl
termination_by structural self

/-- Canonical function types remain unchanged by normalization. -/
private theorem functionTypeNormalized (input : Typ n) (output : Typ m) :
    resolveType (functionType input output) (λ _ => .only) = functionType input output :=
  congr (congrArg Pre.AST.TFn (resolveTypeResolve input (λ _ => .only) 0 0))
    (congrArg Pre.Binder.mk (funext (λ _ => resolveTypeResolve output (λ _ => .only) 1 1)))

/-- Inference always returns types already normalized to context zero. -/
private theorem inferNormalized {trm : Trm n}
    (hInfer : infer trm entries fuel = .yield (some typ)) :
    resolveType typ (λ _ => .only) = typ := by
  induction fuel generalizing n trm entries typ with
  | zero => cases hInfer
  | succ fuel ih =>
    cases trm with
    | val value =>
      cases value with
      | lit repr => cases hInfer; rfl
      | fn input body =>
        cases hBody : infer (body.apply .only) (entries.set (n + 1) ⟨n, input, .empty⟩) fuel <;>
          (try cases ‹Option Typ›) <;> simp_all [infer.eq_3, Rec.Outcome.map, Option.map]
        cases Option.some.inj hInfer
        exact functionTypeNormalized _ _
      | fnPrimitive output op =>
        cases hInfer
        exact functionTypeNormalized _ _
    | ref carrier under =>
      simp only [infer.eq_5] at hInfer
      split at hInfer
      · rename_i context input captured hEntry
        cases Option.some.inj (Rec.Outcome.yield.inj hInfer)
        exact resolveTypeResolve input (λ _ => .only) 0 0
      · exact ih hInfer
      · cases hInfer
    | apply fn arg =>
      simp only [infer.eq_6, Rec.Outcome.flatMap] at hInfer
      repeat split at hInfer
      all_goals try cases hInfer
      exact resolveTypeResolve _ _ 0 0

/-- The input of a successfully inferred function type is already normalized. -/
private theorem inferInputNormalized {trm : Trm n} {input : Typ} {output : Binder 0 .typ}
    (hInfer : infer trm entries fuel = .yield (some (.TFn input output))) :
    resolveType input (λ _ => .only) = input := by
  have hNormal := inferNormalized hInfer
  cases output
  exact (Pre.AST.TFn.inj hNormal).1

private def preservesType (source target : RecOpt Typ) : Prop :=
  ∀ {fuel typ}, source fuel = .yield (some typ) → ∃ targetFuel, target targetFuel = .yield (some typ)

/-- Successful application inference exposes the callee and argument evidence. -/
private theorem inferApplySuccess {fn arg : Trm n}
    (hInfer : infer (.apply fn arg) entries (fuel + 1) = .yield (some typ)) :
    ∃ input output,
      infer fn entries fuel = .yield (some (.TFn input output)) ∧
      infer arg entries fuel = .yield (some input) ∧
      typ = resolveType (output.apply .only) (λ _ => .only) := by
  simp only [infer.eq_6] at hInfer
  split at hInfer
  · rename_i input output argType hFn hArg
    have hNormalArg := inferNormalized hArg
    have hInput := inferInputNormalized hFn
    cases hSame : argType.sameType input fuel with
    | outOfFuel => simp [hSame, Rec.Outcome.flatMap] at hInfer
    | yield accepted =>
      cases accepted with
      | false => simp [hSame, Rec.Outcome.flatMap] at hInfer
      | true =>
        have hEq := sameTypeEq hSame
        rw [hNormalArg, hInput] at hEq
        subst argType
        simp only [hSame, Rec.Outcome.flatMap, ite_true, Rec.Outcome.yield.injEq] at hInfer
        exact ⟨_, _, hFn, hArg, (Option.some.inj hInfer).symm⟩
  all_goals cases hInfer

/-- Successful lambda inference exposes its body type and canonical function type. -/
private theorem inferFnSuccess {input : Typ n} {body : Binder n .trm}
    (hInfer : infer (.val (.fn input body)) entries (fuel + 1) = .yield (some typ)) :
    ∃ output, infer (body.apply .only) (entries.set (n + 1) ⟨n, input, .empty⟩) fuel =
      .yield (some output) ∧ typ = functionType input output := by
  cases hBody : infer (body.apply .only) (entries.set (n + 1) ⟨n, input, .empty⟩) fuel <;>
    (try cases ‹Option Typ›) <;> simp_all [infer.eq_3, Rec.Outcome.map, Option.map]
  exact ⟨_, rfl, (Option.some.inj hInfer).symm⟩

/-- An entry fits a type when either its hypothetical type or its captured value infers that type. -/
private def entryFits (entry : Option (CompilerTyp ⊕ ExeVal)) (typ : Typ) : Prop :=
  ∃ fuel,
    (match entry with
    | some (.inr ⟨_, value, captured⟩) => infer value.asTrm captured fuel
    | some (.inl ⟨_, input, _⟩) => .yield (some (resolveType input (λ _ => .only)))
    | none => .yield none) = .yield (some typ)

/-- Replacing hypothetical entries by inferable runtime values preserves inference. -/
private theorem inferReplace {trm : Trm n} {source target : CompilerBindings}
    (hReplace : ∀ index typ, entryFits (source index) typ → entryFits (target index) typ) :
    preservesType (infer trm source) (infer trm target) := by
  intro fuel typ hInfer
  induction fuel generalizing n trm source target typ with
  | zero => cases hInfer
  | succ fuel ih =>
    cases trm with
    | val value =>
      cases value with
      | lit repr => exact ⟨1, by simpa only [infer.eq_2] using hInfer⟩
      | fn annotation body =>
        obtain ⟨output, hBody, rfl⟩ := inferFnSuccess hInfer
        obtain ⟨bodyFuel, hTarget⟩ := ih (target := target.set (n + 1) ⟨n, annotation, .empty⟩)
          (by
            intro index inputTyp
            simp only [CompilerBindings.get, NatBindings.get]
            split <;> first | exact id | exact hReplace index inputTyp) hBody
        exact ⟨bodyFuel + 1, by simp only [infer.eq_3, hTarget, Rec.Outcome.map]; rfl⟩
      | fnPrimitive _ _ => exact ⟨fuel + 1, by simpa only [infer.eq_4] using hInfer⟩
    | ref carrier under =>
      obtain ⟨targetFuel, hTarget⟩ := hReplace under.sourceIndex.down typ
        ⟨fuel, by
          simp only [infer.eq_5] at hInfer
          split at hInfer <;> simp_all⟩
      exact ⟨targetFuel + 1, by
        simp only [infer.eq_5]
        split <;> simp_all [entryFits]⟩
    | apply fn arg =>
      obtain ⟨input, output, hFn, hArg, rfl⟩ := inferApplySuccess hInfer
      obtain ⟨fnFuel, hFnTarget⟩ := ih hReplace hFn
      obtain ⟨argFuel, hArgTarget⟩ := ih hReplace hArg
      let budget := max (max fnFuel argFuel) 1
      have hFnMore := Monotone.termInfer fn target fnFuel budget _
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hFnTarget
      have hArgMore := Monotone.termInfer arg target argFuel budget _
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hArgTarget
      exact ⟨budget + 1, by
        rw [infer.eq_6, hFnMore, hArgMore]
        have hNormal := inferInputNormalized hFnTarget
        have hMatch := typeMatchesResolve input (λ _ => .only) 0 0
        rw [hNormal] at hMatch
        have hSame : sameType input input budget = .yield true := by
          have hPositive : 0 < budget := by dsimp [budget]; omega
          cases hBudget : budget with
          | zero => rw [hBudget] at hPositive; contradiction
          | succ budget => exact congrArg Rec.Outcome.yield hMatch
        simp only [hSame, Rec.Outcome.flatMap, ite_true]⟩

private def hasType (value : ExeVal) (expected : Typ n) : Rec Bool := λ fuel =>
  (value.value.asTrm.infer value.captured fuel).flatMap (λ actual =>
    match actual with
    | some actual => actual.sameType expected fuel
    | none => .yield false)

/-- A completed runtime type check gives exact inference evidence for the normalized annotation. -/
private theorem hasTypeSound {value : ExeVal} {expected : Typ n}
    (h : hasType value expected fuel = .yield true) :
    value.value.asTrm.infer value.captured fuel =
      .yield (some (resolveType expected (λ _ => .only))) := by
  cases hActual : value.value.asTrm.infer value.captured fuel with
  | outOfFuel => simp [hasType, hActual, Rec.Outcome.flatMap] at h
  | yield result =>
    cases result with
    | none => simp [hasType, hActual, Rec.Outcome.flatMap] at h
    | some actual =>
      have hSame : actual.sameType expected fuel = .yield true := by
        simpa only [hasType, hActual, Rec.Outcome.flatMap] using h
      have hEq := sameTypeEq hSame
      rw [inferNormalized hActual] at hEq
      simp only [hEq]

private def evalInternal {n} (self : Trm n) (bindings : ExeBindings) : Rec (Return ExeVal) := λ fuel =>
  -- TODO: this may be useless and needs to be removed, "eval_certified should build certified result in every step".
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield (.some ⟨n, value, bindings⟩)
    | .ref _ under =>
      match bindings under.sourceIndex.down with
      | some value => .yield (.some value)
      | none => .outOfFuel
    | .apply fn arg =>
      match evalInternal fn bindings fuel, evalInternal arg bindings fuel with
      | .yield (.some ⟨context, .fn input body, captured⟩), .yield (.some argument) =>
        (hasType argument input fuel).flatMap (λ accepted =>
          if accepted then evalInternal (body.apply .only) (captured.set (context + 1) argument) fuel
          else .yield .corrupted)
      | .yield (.some ⟨context, .fnPrimitive output op, captured⟩),
          .yield (.some ⟨_, .lit repr, _⟩) =>
        let value : ExeVal := ⟨context, op repr, captured⟩
        (hasType value (output.apply .only) fuel).map (λ accepted =>
          if accepted then .some value else .corrupted)
      | .yield .corrupted, .yield _
      | .yield _, .yield .corrupted => .yield .corrupted
      | _, _ => .outOfFuel

/-- Every returned closure preserves each successful source inference, including under parameter replacement. -/
private theorem evalPreserves {self : Trm n} {bindings : ExeBindings} {value : ExeVal}
    (hEval : evalInternal self bindings fuel = .yield (.some value)) :
    preservesType (self.infer bindings) (value.value.asTrm.infer value.captured) := by
  intro inferFuel typ hInfer
  induction fuel generalizing n self bindings value inferFuel typ with
  | zero => cases hEval
  | succ fuel ih =>
    cases inferFuel with
    | zero => cases hInfer
    | succ inferFuel =>
      cases self with
      | val source =>
        cases hEval
        exact ⟨inferFuel + 1, hInfer⟩
      | ref carrier under =>
        simp only [evalInternal] at hEval
        split at hEval
        · rename_i result hBinding
          cases hEval
          rcases value with ⟨context, source, captured⟩
          exact ⟨inferFuel, by
            simpa only [infer.eq_5, CompilerBindings.get, CompilerBindings.breakpoint,
              NatBindings.get, hBinding, Option.map, Option.orElse] using hInfer⟩
        · cases hEval
      | apply fn arg =>
        obtain ⟨input, output, hFn, _hArg, rfl⟩ := inferApplySuccess hInfer
        simp only [evalInternal, Rec.Outcome.flatMap, Rec.Outcome.map] at hEval
        split at hEval
        all_goals (repeat split at hEval)
        all_goals try cases hEval
        all_goals subst_vars
        all_goals obtain ⟨_ | fnFuel, hFnValue⟩ := ih (self := fn) (by assumption) hFn
        all_goals try cases hFnValue
        · rename_i context annotation body captured argument hFnEval hArgEval checkResult hCheck
          obtain ⟨bodyTyp, hBody, hFnType⟩ := inferFnSuccess hFnValue
          cases hFnType
          obtain ⟨bodyFuel, hBodyTyped⟩ := inferReplace
            (target := CompilerBindings.breakpoint (captured.set (context + 1) argument))
            (by
              intro index inputTyp hSource
              simp only [CompilerBindings.get, NatBindings.get] at hSource ⊢
              rcases argument with ⟨argContext, argValue, argCaptured⟩
              split at hSource <;> simp_all [entryFits, Option.map]
              exact ⟨fuel, by
                simpa only [Option.some.inj hSource] using hasTypeSound hCheck⟩) hBody
          simp only [Pre.Binder.apply, Pre.Binder.mk, resolveTypeResolve, inferNormalized hBody]
          exact ih hEval hBodyTyped
        · rename_i context expected op captured argContext repr argCaptured hFnEval hArgEval checkResult hCheck
          exact ⟨fuel, by
            simpa only [functionType, Pre.Binder.apply, Pre.Binder.mk, resolveTypeResolve]
              using hasTypeSound hCheck⟩

end CertifiedByInfer

/-- Evaluate an independently inferred term and certify its returned value at the inferred type. -/
def eval_certified (self : Trm n) (bindings : ExeBindings := .empty)
    {inferFuel : Nat} {typ : Typ}
    (_hInfer : self.infer bindings inferFuel = .yield (some typ)) : CertifiedByInfer.Result typ := λ fuel =>
  match hEval : CertifiedByInfer.evalInternal self bindings fuel with
  | .yield (.some value) => .yield (.some ⟨value, by
      obtain ⟨valueFuel, hValue⟩ := CertifiedByInfer.evalPreserves hEval _hInfer
      exact ⟨valueFuel, by rw [hValue]⟩⟩)
  | .yield .corrupted => .yield .corrupted
  | .outOfFuel => .outOfFuel

end Lp2lc.Active.DTLC.AST
