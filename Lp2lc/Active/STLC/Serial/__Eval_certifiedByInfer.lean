import «Lp2lc».Active.STLC.Serial.__Infer

namespace Lp2lc.Active.STLC.AST

open Lp2lc.Active.Util

namespace CertifiedByInfer

/-- A returned value paired with safety under the existing inference rule.

Successful inference preserves the type of the returned value in its captured environment.
-/
structure ResultV2Payload {n} (trm : Trm n) (bindings : ExeBindings) where
  v : ExeValue
  safe : ∀ inferFuel typ, trm.infer bindings inferFuel = .yield (some typ) →
      (v.value.asTrm.infer v.captured).isDecidable (λ inferred => inferred = typ)

/-- Fuel-bounded certified evaluation may still exhaust its fuel. -/
abbrev ResultV2 {n} (trm : Trm n) (bindings : ExeBindings) := Rec (ResultV2Payload trm bindings)

variable {n fuel : Nat} {typ : Typ} {entries : CompilerBindings}

private theorem lookupMap {α β} (bindings : NatBindings α) (f : α → β) (index : Nat) :
    bindings.map f index = (bindings index).map f := by
  rcases bindings with ⟨entries⟩
  induction entries <;> simp_all [NatBindings.map, List.lookup]
  split <;> simp_all

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
    CertifiedByInfer.ResultV2 self bindings := by
  let run : (fuel : Nat) → { result : Rec.OutcomeOpt ExeValue //
      ∀ inferFuel typ, self.infer bindings inferFuel = .yield (some typ) →
        match result with
        | .outOfFuel => True
        | .yield none => False
        | .yield (some value) =>
          ∃ valueFuel, value.value.asTrm.infer value.captured valueFuel = .yield (some typ) } := by
    intro fuel
    induction fuel generalizing n self bindings with
    | zero => exact ⟨.outOfFuel, by intro inferFuel typ hInfer; trivial⟩
    | succ fuel recurse =>
      cases self with
      | val value => exact ⟨.yield (some (.mk n value bindings)),
          by intro inferFuel typ hInfer; exact ⟨inferFuel, hInfer⟩⟩
      | ref carrier under => exact ⟨.yield (bindings under.sourceIndex.down), by
          intro inferFuel typ hInfer
          cases inferFuel with
          | zero => cases hInfer
          | succ inferFuel =>
            cases hBinding : bindings under.sourceIndex.down <;> (try cases ‹ExeValue›)
            all_goals simp only [infer, inferInternal.eq_4, lookupMap, hBinding, Option.map] at hInfer ⊢
            all_goals first | cases hInfer | exact ⟨inferFuel, hInfer⟩⟩
      | apply fn arg =>
        let fnResult := recurse fn bindings
        let argResult := recurse arg bindings
        let result := match fnResult.val, argResult.val with
          | .yield (some (.mk context (.fn _ body) captured)), .yield (some value) =>
            (recurse (body.apply .only) (captured.set (context + 1) value)).val
          | .yield _, .yield _ => .yield none
          | _, _ => .outOfFuel
        refine ⟨result, ?_⟩
        intro inferFuel typ hInfer
        cases inferFuel with
        | zero => cases hInfer
        | succ inferFuel =>
          obtain ⟨input, hFn, hArg⟩ := inferApplySuccess hInfer
          have hFnSafety := fnResult.property inferFuel (.TFn input typ) hFn
          have hArgSafety := argResult.property inferFuel input hArg
          cases hFnEval : fnResult.val <;> cases hArgEval : argResult.val <;>
            (try cases ‹Option ExeValue›) <;> (try cases ‹Option ExeValue›) <;>
            (try cases ‹ExeValue›) <;> (try cases ‹ExeValue›)
          all_goals simp_all [result]
          rename_i context fnValue captured argContext argValue argCaptured
          obtain ⟨fnFuel, hFnValue⟩ := hFnSafety
          obtain ⟨argInferFuel, hArgValue⟩ := hArgSafety
          cases fnFuel with
          | zero => cases hFnValue
          | succ fnFuel =>
            cases fnValue with
            | lit repr => cases Option.some.inj (Rec.Outcome.yield.inj hFnValue)
            | fn annotation body =>
              obtain ⟨fnOutput, hBody, hFnType⟩ := inferFnSuccess hFnValue
              rcases Pre.AST.TFn.inj hFnType with ⟨rfl, rfl⟩
              let bodyBindings := captured.set (context + 1) (.mk argContext argValue argCaptured)
              obtain ⟨bodyFuel, hBodyTarget⟩ := inferReplace
                (target := bodyBindings.map .inl)
                (by
                  have typedArg : entryFits (some (.inl (.mk _ argValue argCaptured)))
                      (resolveType annotation) := ⟨argInferFuel, hArgValue⟩
                  intro index inputTyp hSource
                  simp only [bodyBindings, lookupMap, NatBindings.set, List.lookup] at hSource ⊢
                  split at hSource <;> simp_all [entryFits]) hBody
              simpa only [result, hFnEval, hArgEval] using
                (recurse (body.apply .only) bodyBindings).property bodyFuel _ hBodyTarget
  refine ⟨λ fuel => (run fuel).val, ?_⟩
  intro inferFuel typ hInfer evalFuel
  have safe := (run evalFuel).property inferFuel typ hInfer
  cases hResult : (run evalFuel).val <;> (try cases ‹Option ExeValue›) <;> simp_all
  exact ⟨safe.choose, by rw [safe.choose_spec]⟩

end Lp2lc.Active.STLC.AST
