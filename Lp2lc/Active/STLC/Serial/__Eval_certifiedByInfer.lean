import «Lp2lc».Active.STLC.Serial.__Infer

namespace Lp2lc.Active.STLC.AST

open Lp2lc.Active.Util

namespace CertifiedByInfer

abbrev ConditionalVal (condition : Typ -> Prop) := {v : ExeVal // (v.value.asTrm.infer v.captured).isDecidable condition}

/-- A returned value certified at the caller's independently inferred type. -/
abbrev CertifiedVal (typ : Typ) := ConditionalVal (λ _t => _t = typ)

/-- Fuel-bounded certified evaluation may still exhaust its fuel. -/
abbrev Result (typ : Typ) := Rec (CertifiedVal typ)

variable {n fuel : Nat} {typ : Typ} {entries : CompilerBindings}

private def preservesType (source target : RecOpt Typ) : Prop :=
  ∀ {fuel typ}, source fuel = .yield (some typ) → ∃ targetFuel, target targetFuel = .yield (some typ)

private theorem inferApplySuccess {fn arg : Trm n}
    (hInfer : inferInternal (.apply fn arg) entries (fuel + 1) = .yield (some typ)) :
    ∃ input, inferInternal fn entries fuel = .yield (some (.TFn input typ)) ∧
      inferInternal arg entries fuel = .yield (some input) := by
  simp only [inferInternal.eq_5] at hInfer
  repeat split at hInfer
  all_goals simp_all
  all_goals injection hInfer; subst_vars; exact ⟨_, rfl, rfl⟩

private theorem inferFnSuccess {annotation : Typ n} {body : Binder n .trm}
    (hInfer : inferInternal (.val (.fn annotation body)) entries (fuel + 1) = .yield (some typ)) :
    let input := resolveType annotation
    ∃ output, inferInternal (body.apply .only)
        (entries.set (n + 1) (.inl ⟨n, annotation, .empty⟩)) fuel = .yield (some output) ∧
      typ = .TFn input output := by
  cases hBody : inferInternal (body.apply .only)
      (entries.set (n + 1) (.inl ⟨n, annotation, .empty⟩)) fuel <;>
    (try cases ‹Option Typ›) <;> simp_all [inferInternal.eq_3, Rec.Outcome.map, Option.map]
  exact ⟨_, rfl, (Option.some.inj hInfer).symm⟩

-- Certification uses inference monotonicity and establishes the remaining inference facts locally.
private def entryFits (entry : Option (CompilerTyp ⊕ ExeVal)) (typ : Typ) : Prop :=
  ∃ fuel,
    (match entry with
    | some (.inr ⟨_, value, captured⟩) => inferInternal value.asTrm (captured.map .inr) fuel
    | some (.inl ⟨_, input, _⟩) => .yield (some (resolveType input))
    | none => .yield none) = .yield (some typ)

/-- Replacing hypothetical entries by inferable runtime values preserves inference. -/
private theorem inferReplace {trm : Trm n} {source target : CompilerBindings}
    (hReplace : ∀ index typ, entryFits (source index) typ → entryFits (target index) typ) :
    preservesType (inferInternal trm source) (inferInternal trm target) := by
  intro fuel typ hInfer
  induction fuel generalizing n trm source target typ with
  | zero => cases hInfer
  | succ fuel ih =>
    cases trm with
    | val value =>
      cases value with
      | lit repr => exact ⟨1, by simpa only [inferInternal.eq_2] using hInfer⟩
      | fn annotation body =>
        obtain ⟨output, hBody, rfl⟩ := inferFnSuccess hInfer
        obtain ⟨bodyFuel, hTarget⟩ := ih (target := target.set (n + 1) (.inl ⟨n, annotation, .empty⟩))
          (by
            intro index inputTyp
            simp only [NatBindings.set, List.lookup]
            split <;> first | exact id | exact hReplace index inputTyp) hBody
        exact ⟨bodyFuel + 1, by simp only [inferInternal.eq_3, hTarget, Rec.Outcome.map]; rfl⟩
    | ref carrier under =>
      obtain ⟨targetFuel, hTarget⟩ := hReplace under.sourceIndex.down typ
        ⟨fuel, by
          simp only [inferInternal.eq_4] at hInfer
          split at hInfer <;> simp_all⟩
      exact ⟨targetFuel + 1, by
        simp only [inferInternal.eq_4]
        split <;> simp_all [entryFits]⟩
    | apply fn arg =>
      obtain ⟨input, hFn, hArg⟩ := inferApplySuccess hInfer
      obtain ⟨fnFuel, hFnTarget⟩ := ih hReplace hFn
      obtain ⟨argFuel, hArgTarget⟩ := ih hReplace hArg
      exact ⟨max fnFuel argFuel + 1, by
        rw [inferInternal.eq_5,
          Monotone.termInfer fn target fnFuel (max fnFuel argFuel) _ (Nat.le_max_left _ _) hFnTarget,
          Monotone.termInfer arg target argFuel (max fnFuel argFuel) _ (Nat.le_max_right _ _) hArgTarget]
        exact congrArg _ (ite_eq_left (rfl : input = input))⟩

/-- Each returned value preserves every successful inference of its source term. -/
private def evalInternal {n} (self : Trm n) (bindings : ExeBindings) :
    Rec {value : ExeVal //
      preservesType (self.infer bindings) (value.value.asTrm.infer value.captured)} := λ fuel =>
  match fuel, self with
  | 0, _ => .outOfFuel
  | fuel + 1, .val value => .yield ⟨.mk n value bindings, λ {inferFuel typ} hInfer => ⟨inferFuel, hInfer⟩⟩
  | fuel + 1, .ref _ under =>
    match hBinding : bindings under.sourceIndex.down with
    | none => .outOfFuel
    | some (.mk context value captured) => .yield ⟨.mk context value captured, by
        rintro (_ | inferFuel) typ hInfer
        · cases hInfer
        · simp only [infer, inferInternal.eq_4, NatBindings.getMap, hBinding, Option.map] at hInfer
          exact ⟨inferFuel, by simpa only [infer, NatBindings.map] using hInfer⟩⟩
  | fuel + 1, .apply fn arg =>
    (evalInternal fn bindings fuel).flatMap (λ fnResult =>
      match fnResult with
      | ⟨.mk _ (.lit _) _, _⟩ => .outOfFuel
      | ⟨.mk context (.fn annotation body) captured, fnSafe⟩ =>
        (evalInternal arg bindings fuel).flatMap (λ argResult =>
          let bodyBindings := captured.set (context + 1) argResult.val
          have bodyTyped : preservesType (infer (.apply fn arg) bindings)
              (infer (body.apply .only) bodyBindings) := by
            rintro (_ | inferFuel) typ hInfer
            · cases hInfer
            · obtain ⟨input, hFn, hArg⟩ := inferApplySuccess hInfer
              obtain ⟨_ | fnFuel, hFnValue⟩ := fnSafe hFn
              · cases hFnValue
              · obtain ⟨output, hBody, hFnType⟩ := inferFnSuccess hFnValue
                rcases Pre.AST.TFn.inj hFnType with ⟨rfl, rfl⟩
                rcases argResult with ⟨⟨argContext, argValue, argCaptured⟩, argSafe⟩
                obtain ⟨argFuel, hArgValue⟩ := argSafe hArg
                exact inferReplace (target := bodyBindings.map .inr)
                  (by
                    have typedArg : entryFits (some (.inr ⟨_, argValue, argCaptured⟩))
                        (resolveType annotation) :=
                      ⟨argFuel, hArgValue⟩
                    intro index inputTyp hSource
                    simp only [bodyBindings, NatBindings.getMap, NatBindings.set, List.lookup] at hSource ⊢
                    split at hSource <;> simp_all [entryFits, NatBindings.map]) hBody
          (evalInternal (body.apply .only) bodyBindings fuel).map (λ bodyResult =>
            ⟨bodyResult.val, λ hInfer => (bodyTyped hInfer).elim (λ _ => bodyResult.property)⟩)))

end CertifiedByInfer

open CertifiedByInfer

/-- Evaluate an independently inferred term and certify its returned value at the inferred type. -/
def eval_certified {n} (self : Trm n) (bindings : ExeBindings := .empty)
    {inferFuel : Nat} {typ : Typ}
    (hInfer : self.infer bindings inferFuel = .yield (some typ)) : Result typ := λ fuel =>
  (evalInternal self bindings fuel).map (λ result =>
    ⟨result.val, (result.property hInfer).imp (λ _ hValue => by rw [hValue])⟩)

end Lp2lc.Active.STLC.AST
