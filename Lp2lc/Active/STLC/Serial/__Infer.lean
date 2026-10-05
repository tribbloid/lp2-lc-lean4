import «Lp2lc».Active.STLC.Serial.Eval

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util
namespace AST

/-- Convert a known type to the result context, consuming fuel for each type node. -/
private def resolveType {n} (self : Typ n) : Rec Typ := λ fuel =>
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .TLit => .yield .TLit
    | .TFn tIn tOut =>
      (resolveType tIn fuel).flatMap (λ input =>
        (resolveType tOut fuel).map (.TFn input))

/-- Infer using actual runtime bindings and captured environments, with hypothetical types only under binders. -/
def inferInternal {n} (self : Trm n)
    (bindings : Nat → Option RuntimeValue) : RecOpt Typ :=
  let rec visit {context} (trm : Trm context)
      (entries : Nat → Option (RuntimeValue ⊕ Typ)) : RecOpt Typ := λ fuel =>
    match fuel with
    | 0 => .outOfFuel
    | fuel + 1 =>
      match trm with
      | .val (.lit _) => .yield (some .TLit)
      | .val (.fn tIn body) =>
        (resolveType tIn fuel).flatMap (λ input =>
          (visit (body.apply .only)
            (λ index => if index = context + 2 then some (.inr input)
              else if index = context + 1 then none else entries index) fuel).map
            (Option.map (.TFn input)))
      | .ref _ under =>
        match entries under.sourceIndex with
        | some (.inl (.mk _ value captured)) =>
          visit value.asTrm (λ index => (captured index).map .inl) fuel
        | some (.inr typ) => .yield (some typ)
        | none => .yield none
      | .apply fn arg =>
        match visit fn entries fuel, visit arg entries fuel with
        | .yield (some (.TFn tIn tOut)), .yield (some argTyp) =>
          .yield (if argTyp ≤ tIn then some tOut else none)
        | .yield _, .yield _ => .yield none
        | _, _ => .outOfFuel
  visit self (λ index => (bindings index).map .inl)

/-- Infer with no external runtime bindings. -/
def infer {n} (self : Trm n) : RecOpt Typ :=
  self.inferInternal (λ _ => none)

private theorem resolveTypeMonotone {n} (typ : Typ n) : (resolveType typ).Monotone := by
  intro less more result hFuel hInfer
  induction less generalizing n typ more result with
  | zero => simp [resolveType] at hInfer
  | succ fuel ih =>
    cases more with
    | zero => cases hFuel
    | succ more =>
      have hFuelTail := Nat.le_of_succ_le_succ hFuel
      cases typ <;> simp only [resolveType.eq_2, resolveType.eq_3,
        Rec.Outcome.flatMap, Rec.Outcome.map] at hInfer ⊢
      all_goals
        repeat split at hInfer
        all_goals simp_all
      all_goals
        rename_i tIn tOut _ input hIn _ output hOut
        simp_all [ih tIn more input hFuelTail hIn, ih tOut more output hFuelTail hOut]

private theorem inferVisitMonotone {n} (trm : Trm n)
    (entries : Nat → Option (RuntimeValue ⊕ Typ)) :
    Rec.Monotone (inferInternal.visit trm entries) := by
  intro less more result hFuel hInfer
  induction less generalizing n trm entries more result with
  | zero => simp [inferInternal.visit] at hInfer
  | succ fuel ih =>
    cases more with
    | zero => cases hFuel
    | succ more =>
      have hFuelTail := Nat.le_of_succ_le_succ hFuel
      cases trm <;> try cases ‹Val n›
      all_goals
        simp only [inferInternal.visit.eq_2, inferInternal.visit.eq_3, inferInternal.visit.eq_4, inferInternal.visit.eq_5,
          Rec.Outcome.flatMap, Rec.Outcome.map] at hInfer ⊢
        repeat split at hInfer
        all_goals simp_all
      all_goals simp_all [resolveTypeMonotone _ fuel more _ hFuelTail (by assumption)]

/-- Every completed inference result, including rejection, is preserved when fuel increases. -/
theorem termInferMonotone {n} (trm : Trm n)
    (bindings : Nat → Option RuntimeValue) :
    (inferInternal trm bindings).Monotone :=
  inferVisitMonotone trm (λ index => (bindings index).map .inl)

/-- Value inference monotonicity follows from term inference monotonicity. -/
theorem valueInferMonotone {n} (value : Val n)
    (bindings : Nat → Option RuntimeValue) :
    (inferInternal value.asTrm bindings).Monotone :=
  termInferMonotone value.asTrm bindings

private theorem inferVisitApplySuccess {n} (fn arg : Trm n)
    (entries : Nat → Option (RuntimeValue ⊕ Typ)) (fuel : Nat) (typ : Typ)
    (hInfer : inferInternal.visit (.apply fn arg) entries (fuel + 1) = .yield (some typ)) :
    ∃ input, inferInternal.visit fn entries fuel = .yield (some (.TFn input typ)) ∧
      inferInternal.visit arg entries fuel = .yield (some input) := by
  simp only [inferInternal.visit.eq_5] at hInfer
  repeat split at hInfer
  all_goals simp_all
  all_goals
    change _ = _ at ‹_ ≤ _›
    have hOutput := Option.some.inj hInfer
    subst_vars
    exact ⟨_, rfl, rfl⟩

private theorem inferVisitFnSuccess {n} (annotation : Typ n) (body : Binder (n + 1) .trm)
    (entries : Nat → Option (RuntimeValue ⊕ Typ)) (fuel : Nat) (typ : Typ)
    (hInfer : inferInternal.visit (.val (.fn annotation body)) entries (fuel + 1) = .yield (some typ)) :
    ∃ input output, resolveType annotation fuel = .yield input ∧
      inferInternal.visit (body.apply .only)
        (λ index => if index = n + 2 then some (.inr input)
          else if index = n + 1 then none else entries index) fuel = .yield (some output) ∧
      typ = .TFn input output := by
  simp only [inferInternal.visit.eq_3] at hInfer
  cases hIn : resolveType annotation fuel with
  | outOfFuel => simp [hIn, Rec.Outcome.flatMap] at hInfer
  | yield input =>
    simp only [hIn, Rec.Outcome.flatMap] at hInfer
    cases hBody : inferInternal.visit (body.apply .only)
        (λ index => if index = n + 2 then some (.inr input)
          else if index = n + 1 then none else entries index) fuel with
    | outOfFuel => simp [hBody, Rec.Outcome.map] at hInfer
    | yield result =>
      simp only [hBody, Rec.Outcome.map, Rec.Outcome.yield.injEq] at hInfer
      cases result with
      | none => cases hInfer
      | some output =>
        have hType : .TFn input output = typ := Option.some.inj hInfer
        exact ⟨input, output, rfl, hBody, hType.symm⟩

private theorem inferVisitReplace {n} (trm : Trm n)
    (source target : Nat → Option (RuntimeValue ⊕ Typ)) (fuel : Nat) (typ : Typ)
    (hRuntime : ∀ index value, source index = some (.inl value) →
      target index = some (.inl value))
    (hTypes : ∀ index input, source index = some (.inr input) →
      target index = some (.inr input) ∨
        ∃ context value captured valueFuel,
          target index = some (.inl (.mk context value captured)) ∧
          inferInternal value.asTrm captured valueFuel = .yield (some input))
    (hInfer : inferInternal.visit trm source fuel = .yield (some typ)) :
    ∃ targetFuel, inferInternal.visit trm target targetFuel = .yield (some typ) := by
  induction fuel generalizing n trm source target typ with
  | zero => simp [inferInternal.visit] at hInfer
  | succ fuel ih =>
    cases trm with
    | val value =>
      cases value with
      | lit repr =>
        simp only [inferInternal.visit.eq_2, Rec.Outcome.yield.injEq] at hInfer
        have hType := Option.some.inj hInfer
        subst typ
        exact ⟨1, rfl⟩
      | fn annotation body =>
        obtain ⟨input, output, hIn, hBody, hType⟩ :=
          inferVisitFnSuccess annotation body source fuel typ hInfer
        subst typ
        obtain ⟨bodyFuel, hTarget⟩ := ih (body.apply .only)
          (λ index => if index = n + 2 then some (.inr input)
            else if index = n + 1 then none else source index)
          (λ index => if index = n + 2 then some (.inr input)
            else if index = n + 1 then none else target index) output
          (by
            intro index value hSource
            by_cases hArg : index = n + 2
            · simp [hArg] at hSource
            · by_cases hGhost : index = n + 1
              · simp [hGhost] at hSource
              · simp only [ite_eq_right hArg, ite_eq_right hGhost] at hSource ⊢
                exact hRuntime index value hSource)
          (by
            intro index inputTyp hSource
            by_cases hArg : index = n + 2
            · simp only [ite_eq_left hArg, Option.some.injEq] at hSource
              have hType := Sum.inr.inj hSource
              subst inputTyp
              exact Or.inl (by simp [hArg])
            · by_cases hGhost : index = n + 1
              · simp [hGhost] at hSource
              · simp only [ite_eq_right hArg, ite_eq_right hGhost] at hSource ⊢
                exact hTypes index inputTyp hSource) hBody
        have hInMore := resolveTypeMonotone annotation fuel (max fuel bodyFuel) input
          (Nat.le_max_left _ _) hIn
        have hBodyMore := inferVisitMonotone _ _ bodyFuel (max fuel bodyFuel) (some output)
          (Nat.le_max_right _ _) hTarget
        exact ⟨max fuel bodyFuel + 1, by
          simp only [inferInternal.visit.eq_3, hInMore, hBodyMore, Rec.Outcome.flatMap, Rec.Outcome.map]
          rfl⟩
    | ref carrier under =>
      simp only [inferInternal.visit.eq_4] at hInfer
      cases hEntry : source under.sourceIndex with
      | none => simp [hEntry] at hInfer
      | some entry =>
        cases entry with
        | inl value =>
          have hTarget := hRuntime under.sourceIndex value hEntry
          exact ⟨fuel + 1, by simpa [inferInternal.visit.eq_4, hTarget, hEntry] using hInfer⟩
        | inr input =>
          simp only [hEntry, Rec.Outcome.yield.injEq] at hInfer
          have hType := Option.some.inj hInfer
          subst typ
          rcases hTypes under.sourceIndex input hEntry with hTarget | hTarget
          · exact ⟨1, by simp [inferInternal.visit.eq_4, hTarget]⟩
          · obtain ⟨context, value, captured, valueFuel, hTarget, hValue⟩ := hTarget
            exact ⟨valueFuel + 1, by simpa [inferInternal.visit.eq_4, hTarget, inferInternal] using hValue⟩
    | apply fn arg =>
      obtain ⟨input, hFn, hArg⟩ := inferVisitApplySuccess fn arg source fuel typ hInfer
      obtain ⟨fnFuel, hFnTarget⟩ := ih fn source target (.TFn input typ) hRuntime hTypes hFn
      obtain ⟨argFuel, hArgTarget⟩ := ih arg source target input hRuntime hTypes hArg
      have hFnMore := inferVisitMonotone fn target fnFuel (max fnFuel argFuel) _
        (Nat.le_max_left _ _) hFnTarget
      have hArgMore := inferVisitMonotone arg target argFuel (max fnFuel argFuel) _
        (Nat.le_max_right _ _) hArgTarget
      exact ⟨max fnFuel argFuel + 1, by
        simp only [inferInternal.visit.eq_5, hFnMore, hArgMore]
        have hRefl : input ≤ input := rfl
        simp [hRefl]⟩

private theorem inferEvalSafetyAtFuel {n} (trm : Trm n)
    (bindings : Nat → Option RuntimeValue) (evalFuel inferFuel : Nat) (typ : Typ)
    (hInfer : inferInternal trm bindings inferFuel = .yield (some typ)) :
    match eval trm bindings evalFuel with
    | .outOfFuel => True
    | .yield none => False
    | .yield (some (.mk _ value captured)) =>
      ∃ valueFuel, inferInternal value.asTrm captured valueFuel = .yield (some typ) := by
  induction evalFuel generalizing n trm bindings inferFuel typ with
  | zero => trivial
  | succ evalFuel ih =>
    cases trm with
    | val value => exact ⟨inferFuel, hInfer⟩
    | ref carrier under =>
      cases inferFuel with
      | zero => simp [inferInternal, inferInternal.visit] at hInfer
      | succ inferFuel =>
        cases hBinding : bindings under.sourceIndex with
        | none => simp [inferInternal, inferInternal.visit.eq_4, hBinding] at hInfer
        | some value =>
          cases value with
          | mk context value captured =>
            simp only [eval.eq_3, hBinding]
            exact ⟨inferFuel, by simpa [inferInternal, inferInternal.visit.eq_4, hBinding] using hInfer⟩
    | apply fn arg =>
      cases inferFuel with
      | zero => simp [inferInternal, inferInternal.visit] at hInfer
      | succ inferFuel =>
        obtain ⟨input, hFn, hArg⟩ := inferVisitApplySuccess fn arg
          (λ index => (bindings index).map .inl) inferFuel typ hInfer
        have hFnSafety := ih fn bindings inferFuel (.TFn input typ) hFn
        have hArgSafety := ih arg bindings inferFuel input hArg
        cases hFnEval : eval fn bindings evalFuel with
        | outOfFuel =>
          cases eval arg bindings evalFuel <;> simp [eval.eq_4, hFnEval]
        | yield fnResult =>
          cases fnResult with
          | none => simp [hFnEval] at hFnSafety
          | some runtimeFn =>
            cases runtimeFn with
            | mk context fnValue captured =>
              simp only [hFnEval] at hFnSafety
              obtain ⟨fnInferFuel, hFnValue⟩ := hFnSafety
              cases fnValue with
              | lit repr =>
                cases fnInferFuel with
                | zero => simp [inferInternal, inferInternal.visit] at hFnValue
                | succ fnInferFuel =>
                  simp only [inferInternal, Val.asTrm, inferInternal.visit.eq_2, Rec.Outcome.yield.injEq] at hFnValue
                  cases Option.some.inj hFnValue
              | fn annotation body =>
                cases hArgEval : eval arg bindings evalFuel with
                | outOfFuel => simp [eval.eq_4, hFnEval, hArgEval]
                | yield argResult =>
                  cases argResult with
                  | none => simp [hArgEval] at hArgSafety
                  | some runtimeArg =>
                    cases runtimeArg with
                    | mk argContext argValue argCaptured =>
                      simp only [hArgEval] at hArgSafety
                      obtain ⟨argInferFuel, hArgValue⟩ := hArgSafety
                      cases fnInferFuel with
                      | zero => simp [inferInternal, inferInternal.visit] at hFnValue
                      | succ fnInferFuel =>
                        obtain ⟨fnInput, fnOutput, _, hBody, hFnType⟩ :=
                          inferVisitFnSuccess annotation body
                            (λ index => (captured index).map .inl)
                            fnInferFuel (.TFn input typ) hFnValue
                        have hEqual := Pre.AST.TFn.inj hFnType
                        rcases hEqual with ⟨hInput, hOutput⟩
                        subst fnInput
                        subst fnOutput
                        let bodyBindings := λ index =>
                          if index = context + 2 then some (.mk argContext argValue argCaptured)
                            else if index = context + 1 then none else captured index
                        obtain ⟨bodyFuel, hBodyTarget⟩ := inferVisitReplace (body.apply .only)
                          (λ index => if index = context + 2 then some (.inr input)
                            else if index = context + 1 then none else (captured index).map .inl)
                          (λ index => (bodyBindings index).map .inl) fnInferFuel typ
                          (by
                            intro index value hSource
                            by_cases hArgIndex : index = context + 2
                            · simp [hArgIndex] at hSource
                            · by_cases hGhost : index = context + 1
                              · simp [hGhost] at hSource
                              · simpa [bodyBindings, hArgIndex, hGhost] using hSource)
                          (by
                            intro index inputTyp hSource
                            by_cases hArgIndex : index = context + 2
                            · simp only [ite_eq_left hArgIndex, Option.some.injEq] at hSource
                              have hType := Sum.inr.inj hSource
                              subst inputTyp
                              exact Or.inr ⟨argContext, argValue, argCaptured, argInferFuel,
                                by simp [bodyBindings, hArgIndex], hArgValue⟩
                            · by_cases hGhost : index = context + 1
                              · simp [hGhost] at hSource
                              · simp only [ite_eq_right hArgIndex, ite_eq_right hGhost] at hSource
                                cases hCaptured : captured index <;> simp [hCaptured] at hSource)
                          hBody
                        have hBodySafety := ih (body.apply .only) bodyBindings bodyFuel typ hBodyTarget
                        simpa [eval.eq_4, hFnEval, hArgEval, bodyBindings] using hBodySafety

/-- Successful inference excludes evaluation rejection and preserves the inferred type of every result. -/
theorem inferEvalSafety {n} (trm : Trm n) (bindings : Nat → Option RuntimeValue)
    (inferFuel : Nat) (typ : Typ)
    (hInfer : inferInternal trm bindings inferFuel = .yield (some typ)) :
    (eval trm bindings).isSemiDecidable (λ result =>
      match result with
      | .mk _ value captured =>
        ∃ valueFuel, inferInternal value.asTrm captured valueFuel = .yield (some typ)) := by
  intro evalFuel
  have hSafety := inferEvalSafetyAtFuel trm bindings evalFuel inferFuel typ hInfer
  cases hEval : eval trm bindings evalFuel with
  | outOfFuel => trivial
  | yield result =>
    cases result with
    | none => simp [hEval] at hSafety
    | some value =>
      cases value
      simpa [hEval] using hSafety

end AST
end Lp2lc.Active.STLC
