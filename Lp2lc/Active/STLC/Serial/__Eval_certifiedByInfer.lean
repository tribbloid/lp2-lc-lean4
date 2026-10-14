import «Lp2lc».Active.STLC.Serial.__Infer

namespace Lp2lc.Active.STLC.AST

open Lp2lc.Active.Util

namespace CertifiedByInfer

/-- A returned value paired with safety under the existing inference rule.

Successful inference preserves the type of the returned value in its captured environment.
-/
structure ResultPayload {n} (trm : Trm n) (bindings : ExeBindings) where
  v : ExeValue
  safe : ∀ inferFuel typ, trm.infer bindings inferFuel = .yield (some typ) →
      (v.value.asTrm.infer v.captured).isDecidable (λ inferred => inferred = typ)

/-- Fuel-bounded certified evaluation may still exhaust its fuel. -/
abbrev Result {n} (trm : Trm n) (bindings : ExeBindings) := Rec (ResultPayload trm bindings)

variable {n fuel : Nat} {typ : Typ} {entries : CompilerBindings}

private theorem lookupMap {α β} (bindings : NatBindings α) (f : α → β) (index : Nat) :
    bindings.map f index = (bindings index).map f := by
  rcases bindings with ⟨entries⟩
  induction entries <;> simp_all [NatBindings.map, List.lookup]
  split <;> simp_all

private theorem inferWitness {trm : Trm n} {bindings : ExeBindings}
    (hInfer : (trm.infer bindings).isDecidable (λ inferred => inferred = typ)) :
    ∃ fuel, trm.infer bindings fuel = .yield (some typ) := by
  obtain ⟨fuel, hInfer⟩ := hInfer
  cases hResult : trm.infer bindings fuel <;> (try cases ‹Option Typ›) <;> simp_all
  exact ⟨fuel, hResult⟩

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
        (entries.set (n + 1) (.inr input)) fuel = .yield (some output) ∧
      typ = .TFn input output := by
  cases hBody : inferInternal (body.apply .only)
      (entries.set (n + 1) (.inr (resolveType annotation))) fuel <;>
    (try cases ‹Option Typ›) <;> simp_all [inferInternal.eq_3, Rec.Outcome.map, Option.map]
  exact ⟨_, rfl, (Option.some.inj hInfer).symm⟩

-- Certification reuses inference monotonicity and derives its other inference facts locally.
private def entryFits (entry : Option ValOrTyp) (typ : Typ) : Prop :=
  match entry with
  | none => False
  | some (.inr input) => input = typ
  | some (.inl (.mk _ value captured)) =>
    ∃ fuel, inferInternal value.asTrm (captured.map .inl) fuel = .yield (some typ)

/-- Replacing hypothetical entries by inferable runtime values preserves inference. -/
private theorem inferReplace {trm : Trm n} {source target : CompilerBindings}
    (hReplace : ∀ index typ, entryFits (source index) typ → entryFits (target index) typ)
    (hInfer : inferInternal trm source fuel = .yield (some typ)) :
    ∃ targetFuel, inferInternal trm target targetFuel = .yield (some typ) := by
  induction fuel generalizing n trm source target typ with
  | zero => cases hInfer
  | succ fuel ih =>
    cases trm with
    | val value =>
      cases value with
      | lit repr => exact ⟨1, by simpa only [inferInternal.eq_2] using hInfer⟩
      | fn annotation body =>
        obtain ⟨output, hBody, hType⟩ := inferFnSuccess hInfer
        subst typ
        obtain ⟨bodyFuel, hTarget⟩ := ih (target := target.set (n + 1) (.inr (resolveType annotation)))
          (by intro index inputTyp; simp only [NatBindings.set, List.lookup]; split <;> simp_all) hBody
        exact ⟨bodyFuel + 1, by simp only [inferInternal.eq_3, hTarget, Rec.Outcome.map]; rfl⟩
    | ref carrier under =>
      simp only [inferInternal.eq_4] at hInfer
      have hTarget := hReplace under.sourceIndex.down typ (by
        cases hEntry : source under.sourceIndex.down <;> (try cases ‹ValOrTyp›) <;> (try cases ‹ExeValue›)
        all_goals simp only [hEntry, entryFits, Rec.Outcome.yield.injEq] at hInfer ⊢
        all_goals first | (cases hInfer <;> rfl) | exact ⟨fuel, hInfer⟩ | exact Option.some.inj hInfer)
      cases hEntry : target under.sourceIndex.down <;> (try cases ‹ValOrTyp›) <;> (try cases ‹ExeValue›)
      all_goals simp only [hEntry, entryFits] at hTarget
      all_goals
        first
        | contradiction
        | (obtain ⟨valueFuel, hValue⟩ := hTarget
           exact ⟨valueFuel + 1, by rw [inferInternal.eq_4, hEntry]; exact hValue⟩)
        | exact ⟨1, by simp [inferInternal.eq_4, hEntry, hTarget]⟩
    | apply fn arg =>
      obtain ⟨input, hFn, hArg⟩ := inferApplySuccess hInfer
      obtain ⟨fnFuel, hFnTarget⟩ := ih hReplace hFn
      obtain ⟨argFuel, hArgTarget⟩ := ih hReplace hArg
      have hFnMore := Monotone.termInfer fn target fnFuel (max fnFuel argFuel) _
        (Nat.le_max_left _ _) hFnTarget
      have hArgMore := Monotone.termInfer arg target argFuel (max fnFuel argFuel) _
        (Nat.le_max_right _ _) hArgTarget
      exact ⟨max fnFuel argFuel + 1, by
        simp only [inferInternal.eq_5, hFnMore, hArgMore]
        exact congrArg Rec.Outcome.yield (ite_eq_left (rfl : input = input))⟩

end CertifiedByInfer

open CertifiedByInfer

/-- Evaluate with an erased safety proof constructed at every recursive step.

Each yielded payload contains the value and its certificate. No typing
witness is needed to run evaluation; `safe` applies to any successful inference
of the original term, with an independent inference fuel budget.
-/
def eval_certified {n} (self : Trm n) (bindings : ExeBindings := .empty) :
    Result self bindings := λ fuel =>
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield ⟨.mk n value bindings, by
        intro inferFuel typ hInfer
        exact ⟨inferFuel, by simp only [Val.asTrm, hInfer]; rfl⟩⟩
    | .ref _ under =>
      match hBinding : bindings under.sourceIndex.down with
      | none => .outOfFuel
      | some (.mk context value captured) => .yield ⟨.mk context value captured, by
          intro inferFuel typ hInfer
          cases inferFuel with
          | zero => cases hInfer
          | succ inferFuel =>
            simp only [infer, inferInternal.eq_4, lookupMap, hBinding, Option.map] at hInfer
            exact ⟨inferFuel, by simp only [infer, hInfer]; rfl⟩⟩
    | .apply fn arg =>
      (eval_certified fn bindings fuel).flatMap (λ fnResult =>
        (eval_certified arg bindings fuel).flatMap (λ argResult =>
          match fnResult with
          | ⟨.mk _ (.lit _) _, _⟩ => .outOfFuel
          | ⟨.mk context (.fn annotation body) captured, fnSafe⟩ =>
            let bodyBindings := captured.set (context + 1) argResult.v
            (eval_certified (body.apply .only) bodyBindings fuel).map (λ bodyResult => ⟨bodyResult.v, by
              intro inferFuel typ hInfer
              cases inferFuel with
              | zero => cases hInfer
              | succ inferFuel =>
                rcases argResult with ⟨⟨argContext, argValue, argCaptured⟩, argSafe⟩
                obtain ⟨input, hFn, hArg⟩ := inferApplySuccess hInfer
                obtain ⟨fnFuel, hFnValue⟩ := inferWitness (fnSafe inferFuel (.TFn input typ) hFn)
                obtain ⟨argInferFuel, hArgValue⟩ := inferWitness (argSafe inferFuel input hArg)
                cases fnFuel with
                | zero => cases hFnValue
                | succ fnFuel =>
                  obtain ⟨fnOutput, hBody, hFnType⟩ := inferFnSuccess hFnValue
                  rcases Pre.AST.TFn.inj hFnType with ⟨rfl, rfl⟩
                  obtain ⟨bodyFuel, hBodyTarget⟩ := inferReplace
                    (target := bodyBindings.map .inl)
                    (by
                      have typedArg : entryFits (some (.inl (.mk _ argValue argCaptured)))
                          (resolveType annotation) := ⟨argInferFuel, hArgValue⟩
                      intro index inputTyp hSource
                      simp only [bodyBindings, lookupMap, NatBindings.set, List.lookup] at hSource ⊢
                      split at hSource <;> simp_all [entryFits]) hBody
                  exact bodyResult.safe bodyFuel _ hBodyTarget⟩)))

end Lp2lc.Active.STLC.AST
