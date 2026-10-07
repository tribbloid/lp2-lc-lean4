import «Lp2lc».Active.STLC.Serial.__Infer

namespace Lp2lc.Active.STLC.AST

open Lp2lc.Active.Util
open Lp2lc.Active.STLC.AST

variable {n} (trm : Trm n) (bindings : ExeBindings)

namespace Fundamental

def safety (typ : Typ) : Prop :=
  (trm.eval bindings).isSemiDecidable (λ result =>
    (result.value.asTrm.infer result.captured).isDecidable (λ inferred => inferred ≤ typ))

private theorem inferApplySuccess (fn arg : Trm n)
    (entries : BuildBindings) (fuel : Nat) (typ : Typ)
    (hInfer : inferInternal (.apply fn arg) entries (fuel + 1) = .yield (some typ)) :
    ∃ input, inferInternal fn entries fuel = .yield (some (.TFn input typ)) ∧
      inferInternal arg entries fuel = .yield (some input) := by
  simp only [inferInternal.eq_5] at hInfer
  repeat split at hInfer
  all_goals simp_all
  all_goals
    change _ = _ at ‹_ ≤ _›
    have hOutput := Option.some.inj hInfer
    subst_vars
    exact ⟨_, rfl, rfl⟩

private theorem inferFnSuccess (annotation : Typ n) (body : Binder n .trm)
    (entries : BuildBindings) (fuel : Nat) (typ : Typ)
    (hInfer : inferInternal (.val (.fn annotation body)) entries (fuel + 1) = .yield (some typ)) :
    let input := resolveType annotation
    ∃ output, inferInternal (body.apply .only)
        (λ index => if index = n + 1 then some (.inr input) else entries index) fuel = .yield (some output) ∧
      typ = .TFn input output := by
  simp only [inferInternal.eq_3, Rec.Outcome.map] at hInfer
  repeat split at hInfer
  all_goals simp_all
  all_goals cases ‹Option Typ› <;> simp only [Option.map] at hInfer
  all_goals try cases hInfer
  all_goals exact ⟨_, rfl, rfl⟩

private def EntryFits (entry : Option ValOrTyp) (typ : Typ) : Prop :=
  match entry with
  | none => False
  | some (.inr input) => input = typ
  | some (.inl (.mk _ value captured)) =>
    ∃ fuel, inferInternal value.asTrm (Option.map .inl ∘ captured) fuel = .yield (some typ)

private theorem inferReplace (trm : Trm n)
    (source target : BuildBindings) (fuel : Nat) (typ : Typ)
    (hReplace : ∀ index typ, EntryFits (source index) typ → EntryFits (target index) typ)
    (hInfer : inferInternal trm source fuel = .yield (some typ)) :
    ∃ targetFuel, inferInternal trm target targetFuel = .yield (some typ) := by
  induction fuel generalizing n trm source target typ with
  | zero => simp [inferInternal] at hInfer
  | succ fuel ih =>
    cases trm with
    | val value =>
      cases value with
      | lit repr =>
        simp only [inferInternal.eq_2, Rec.Outcome.yield.injEq] at hInfer
        have hType := Option.some.inj hInfer
        subst typ
        exact ⟨1, rfl⟩
      | fn annotation body =>
        let input := resolveType annotation
        obtain ⟨output, hBody, hType⟩ :=
          inferFnSuccess annotation body source fuel typ hInfer
        subst typ
        obtain ⟨bodyFuel, hTarget⟩ := ih (body.apply .only)
          (λ index => if index = n + 1 then some (.inr input) else source index)
          (λ index => if index = n + 1 then some (.inr input) else target index) output
          (by intro index inputTyp; split <;> simp_all) hBody
        dsimp only [input] at hTarget
        exact ⟨bodyFuel + 1, by
          simp only [inferInternal.eq_3, hTarget, Rec.Outcome.map]
          rfl⟩
    | ref carrier under =>
      simp only [inferInternal.eq_4] at hInfer
      have hFit : EntryFits (source under.sourceIndex) typ := by
        cases hEntry : source under.sourceIndex <;> (try cases ‹ValOrTyp›) <;> (try cases ‹ExeValue›)
        all_goals simp only [hEntry, EntryFits, Rec.Outcome.yield.injEq] at hInfer ⊢
        all_goals first | (cases hInfer <;> rfl) | exact ⟨fuel, hInfer⟩ | exact Option.some.inj hInfer
      have hTarget := hReplace under.sourceIndex typ hFit
      cases hEntry : target under.sourceIndex <;> (try cases ‹ValOrTyp›) <;> (try cases ‹ExeValue›)
      all_goals simp only [hEntry, EntryFits] at hTarget
      all_goals
        first
        | contradiction
        | (obtain ⟨valueFuel, hValue⟩ := hTarget
           exact ⟨valueFuel + 1, by rw [inferInternal.eq_4, hEntry]; exact hValue⟩)
        | exact ⟨1, by simp [inferInternal.eq_4, hEntry, hTarget]⟩
    | apply fn arg =>
      obtain ⟨input, hFn, hArg⟩ := inferApplySuccess fn arg source fuel typ hInfer
      obtain ⟨fnFuel, hFnTarget⟩ := ih fn source target (.TFn input typ) hReplace hFn
      obtain ⟨argFuel, hArgTarget⟩ := ih arg source target input hReplace hArg
      have hFnMore := Monotone.termInfer fn target fnFuel (max fnFuel argFuel) _
        (Nat.le_max_left _ _) hFnTarget
      have hArgMore := Monotone.termInfer arg target argFuel (max fnFuel argFuel) _
        (Nat.le_max_right _ _) hArgTarget
      exact ⟨max fnFuel argFuel + 1, by
        simp only [inferInternal.eq_5, hFnMore, hArgMore]
        have hRefl : input ≤ input := rfl
        simp [hRefl]⟩

/-- Successful inference excludes evaluation rejection and preserves the inferred type of every result. -/
theorem inferEvalSafety (trm : Trm n) (bindings : ExeBindings)
    (inferFuel : Nat) (typ : Typ)
    (hInfer : infer trm bindings inferFuel = .yield (some typ)) :
    (eval trm bindings).isSemiDecidable (λ result =>
      ∃ valueFuel, infer result.value.asTrm result.captured valueFuel = .yield (some typ)) := by
  intro evalFuel
  induction evalFuel generalizing n trm bindings inferFuel typ with
  | zero => trivial
  | succ evalFuel ih =>
    cases inferFuel with
    | zero => simp [infer, inferInternal] at hInfer
    | succ inferFuel =>
      cases trm with
      | val value => exact ⟨inferFuel + 1, hInfer⟩
      | ref carrier under =>
        cases hBinding : bindings under.sourceIndex with
        | none => simp [infer, inferInternal.eq_4, hBinding, Option.map] at hInfer
        | some value =>
          rcases value with ⟨context, value, captured⟩
          simp only [eval.eq_3, hBinding]
          exact ⟨inferFuel, by simpa [infer, inferInternal.eq_4, hBinding, Option.map] using hInfer⟩
      | apply fn arg =>
        obtain ⟨input, hFn, hArg⟩ := inferApplySuccess fn arg
          (Option.map .inl ∘ bindings) inferFuel typ hInfer
        have hFnSafety := ih fn bindings inferFuel (.TFn input typ) hFn
        have hArgSafety := ih arg bindings inferFuel input hArg
        cases hFnEval : eval fn bindings evalFuel with
        | outOfFuel =>
          cases eval arg bindings evalFuel <;> simp [eval.eq_4, hFnEval]
        | yield fnResult =>
          cases fnResult with
          | none => simp [hFnEval] at hFnSafety
          | some runtimeFn =>
            rcases runtimeFn with ⟨context, fnValue, captured⟩
            simp only [hFnEval] at hFnSafety
            obtain ⟨fnInferFuel, hFnValue⟩ := hFnSafety
            cases fnInferFuel with
            | zero => simp [infer, inferInternal] at hFnValue
            | succ fnInferFuel =>
              cases fnValue with
              | lit repr =>
                simp only [Val.asTrm, infer, inferInternal.eq_2, Rec.Outcome.yield.injEq] at hFnValue
                cases Option.some.inj hFnValue
              | fn annotation body =>
                cases hArgEval : eval arg bindings evalFuel with
                | outOfFuel => simp [eval.eq_4, hFnEval, hArgEval]
                | yield argResult =>
                  cases argResult with
                  | none => simp [hArgEval] at hArgSafety
                  | some runtimeArg =>
                    rcases runtimeArg with ⟨argContext, argValue, argCaptured⟩
                    simp only [hArgEval] at hArgSafety
                    obtain ⟨argInferFuel, hArgValue⟩ := hArgSafety
                    obtain ⟨fnOutput, hBody, hFnType⟩ :=
                      inferFnSuccess annotation body (Option.map .inl ∘ captured)
                        fnInferFuel (.TFn input typ) hFnValue
                    rcases Pre.AST.TFn.inj hFnType with ⟨hInput, hOutput⟩
                    subst fnOutput
                    rw [← hInput] at hBody
                    let bodyBindings := λ index =>
                      if index = context + 1 then some (.mk argContext argValue argCaptured) else captured index
                    obtain ⟨bodyFuel, hBodyTarget⟩ := inferReplace (body.apply .only)
                      (λ index => if index = context + 1 then some (.inr input) else (captured index).map .inl)
                      (Option.map .inl ∘ bodyBindings) fnInferFuel typ
                      (by
                        intro index inputTyp hSource
                        by_cases hIndex : index = context + 1
                        · simp only [hIndex, ite_eq_left, EntryFits] at hSource
                          subst inputTyp
                          simp only [Function.comp_apply, bodyBindings, hIndex, ite_eq_left, Option.map, EntryFits]
                          exact ⟨argInferFuel, hArgValue⟩
                        · simpa [bodyBindings, hIndex] using hSource)
                      hBody
                    simpa [eval.eq_4, hFnEval, hArgEval, bodyBindings] using
                      ih (body.apply .only) bodyBindings bodyFuel typ hBodyTarget

/-- A successfully inferred type makes the executable term safe at that type. -/
theorem main (fuel : Nat) (typ : Typ)
    (hInfer : trm.infer bindings fuel = .yield (some typ)) :
    safety trm bindings typ := by
  intro evalFuel
  have safe := inferEvalSafety trm bindings fuel typ hInfer evalFuel
  cases result : trm.eval bindings evalFuel <;> (try cases ‹Option ExeValue›) <;> (try cases ‹ExeValue›) <;>
    simp_all
  obtain ⟨valueFuel, typed⟩ := safe
  exact ⟨valueFuel, by rw [typed]; exact (rfl : typ ≤ typ)⟩

/--
If compilation succeeds, the term must be safe.

TODO: this is the "Paranoid Fundamental theorem": compilation may fail even when term evaluation succeeds.
-/
theorem paranoid :
    (trm.infer bindings).ifSucceedMustSatisfy (safety trm bindings) := by
  intro fuel
  cases result : trm.infer bindings fuel <;> (try cases ‹Option Typ›) <;>
    first | trivial | exact main trm bindings fuel _ result

end Fundamental

end Lp2lc.Active.STLC.AST
