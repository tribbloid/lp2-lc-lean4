import «Lp2lc».Active.STLC.Serial.__Infer
import «Lp2lc».Active.STLC.Serial.Eval

namespace Lp2lc.Active.STLC.AST

open Lp2lc.Active.Util

variable {n} (trm : Trm n) (bindings : ExeBindings)

namespace Fundamental

def safety (typ : Typ) : Prop :=
  (trm.eval bindings).isSemiDecidable (λ result =>
    (result.value.asTrm.infer result.captured).isDecidable (λ inferred => inferred = typ))

private theorem inferApplySuccess {fn arg : Trm n}
    {entries : CompilerBindings} {fuel : Nat} {typ : Typ}
    (hInfer : infer (.apply fn arg) entries (fuel + 1) = .yield (some typ)) :
    ∃ input, infer fn entries fuel = .yield (some (.TFn input typ)) ∧
      infer arg entries fuel = .yield (some input) := by
  simp only [infer.eq_5] at hInfer
  repeat split at hInfer
  all_goals simp_all
  all_goals injection hInfer; subst_vars; exact ⟨_, rfl, rfl⟩

private theorem inferFnSuccess {annotation : Typ n} {body : Binder n .trm}
    {entries : CompilerBindings} {fuel : Nat} {typ : Typ}
    (hInfer : infer (.val (.fn annotation body)) entries (fuel + 1) = .yield (some typ)) :
    let input := resolveType annotation
    ∃ output, infer (body.apply .only)
        (entries.set (n + 1) ⟨n, annotation, .empty⟩) fuel = .yield (some output) ∧
      typ = .TFn input output := by
  simp only [infer.eq_3, Rec.Outcome.map] at hInfer
  repeat split at hInfer
  all_goals simp_all
  all_goals cases ‹Option Typ› <;> simp only [Option.map] at hInfer
  all_goals try cases hInfer
  all_goals exact ⟨_, rfl, rfl⟩

private def entryFits (entry : Option (CompilerTyp ⊕ ExeVal)) (typ : Typ) : Prop :=
  match entry with
  | none => False
  | some (.inl ⟨_, input, _⟩) => resolveType input = typ
  | some (.inr ⟨_, value, captured⟩) =>
    ∃ fuel, infer value.asTrm captured fuel = .yield (some typ)

private theorem inferReplace {trm : Trm n}
    {source target : CompilerBindings} {fuel : Nat} {typ : Typ}
    (hReplace : ∀ index typ, entryFits (source index) typ → entryFits (target index) typ)
    (hInfer : infer trm source fuel = .yield (some typ)) :
    ∃ targetFuel, infer trm target targetFuel = .yield (some typ) := by
  induction fuel generalizing n trm source target typ with
  | zero => simp [infer] at hInfer
  | succ fuel ih =>
    cases trm with
    | val value =>
      cases value with
      | lit repr =>
        exact ⟨1, by simpa only [infer.eq_2] using hInfer⟩
      | fn annotation body =>
        obtain ⟨output, hBody, hType⟩ := inferFnSuccess hInfer
        subst typ
        obtain ⟨bodyFuel, hTarget⟩ := ih (target := target.set (n + 1) ⟨n, annotation, .empty⟩)
          (by
            intro index inputTyp
            simp only [CompilerBindings.get]
            split <;> first | exact id | exact hReplace index inputTyp) hBody
        exact ⟨bodyFuel + 1, by simp only [infer.eq_3, hTarget, Rec.Outcome.map]; rfl⟩
    | ref carrier under =>
      simp only [infer.eq_4] at hInfer
      have hFit : entryFits (source under.sourceIndex.down) typ := by
        split at hInfer <;> simp_all [entryFits]
        all_goals first | exact ⟨fuel, hInfer⟩ | exact Option.some.inj hInfer
      have hTarget := hReplace under.sourceIndex.down typ hFit
      unfold entryFits at hTarget
      split at hTarget
      · contradiction
      · exact ⟨1, by simp_all [infer.eq_4]⟩
      · obtain ⟨valueFuel, hValue⟩ := hTarget
        exact ⟨valueFuel + 1, by simp_all [infer.eq_4]⟩
    | apply fn arg =>
      obtain ⟨input, hFn, hArg⟩ := inferApplySuccess hInfer
      obtain ⟨fnFuel, hFnTarget⟩ := ih hReplace hFn
      obtain ⟨argFuel, hArgTarget⟩ := ih hReplace hArg
      have hFnMore := Monotone.termInfer fn target fnFuel (max fnFuel argFuel) _
        (Nat.le_max_left _ _) hFnTarget
      have hArgMore := Monotone.termInfer arg target argFuel (max fnFuel argFuel) _
        (Nat.le_max_right _ _) hArgTarget
      exact ⟨max fnFuel argFuel + 1, by
        simp only [infer.eq_5, hFnMore, hArgMore]
        exact congrArg Rec.Outcome.yield (ite_eq_left (rfl : input = input))⟩

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
    | zero => simp [infer] at hInfer
    | succ inferFuel =>
      cases trm with
      | val value => exact ⟨inferFuel + 1, hInfer⟩
      | ref carrier under =>
        cases hBinding : bindings under.sourceIndex.down <;> (try cases ‹ExeVal›)
        all_goals simp only [infer, infer.eq_4, CompilerBindings.get, hBinding,
          Option.map, eval.eq_3] at hInfer ⊢
        all_goals first | cases hInfer | exact ⟨inferFuel, hInfer⟩
      | apply fn arg =>
        obtain ⟨input, hFn, hArg⟩ := inferApplySuccess hInfer
        have hFnSafety := ih fn bindings inferFuel (.TFn input typ) hFn
        have hArgSafety := ih arg bindings inferFuel input hArg
        cases hFnEval : eval fn bindings evalFuel <;> (try cases ‹Option ExeVal›) <;> (try cases ‹ExeVal›)
        all_goals simp [hFnEval] at hFnSafety
        case outOfFuel =>
          cases eval arg bindings evalFuel <;> simp [eval.eq_4, hFnEval]
        case yield.some.mk context fnValue captured =>
          obtain ⟨fnInferFuel, hFnValue⟩ := hFnSafety
          cases fnInferFuel with
          | zero => simp [infer] at hFnValue
          | succ fnInferFuel =>
            cases fnValue with
            | lit repr =>
              simp only [Val.asTrm, infer, infer.eq_2, Rec.Outcome.yield.injEq] at hFnValue
              cases Option.some.inj hFnValue
            | fn annotation body =>
                cases hArgEval : eval arg bindings evalFuel <;> (try cases ‹Option ExeVal›) <;> (try cases ‹ExeVal›)
                all_goals simp [hArgEval] at hArgSafety
                case outOfFuel => simp [eval.eq_4, hFnEval, hArgEval]
                case yield.some.mk argContext argValue argCaptured =>
                  obtain ⟨argInferFuel, hArgValue⟩ := hArgSafety
                  obtain ⟨fnOutput, hBody, hFnType⟩ := inferFnSuccess hFnValue
                  rcases Pre.AST.TFn.inj hFnType with ⟨hInput, hOutput⟩
                  subst fnOutput
                  let bodyBindings := captured.set (context + 1) (.mk argContext argValue argCaptured)
                  obtain ⟨bodyFuel, hBodyTarget⟩ := inferReplace (target := bodyBindings)
                    (by
                      have typedArg : entryFits (some (.inr ⟨_, argValue, argCaptured⟩)) input :=
                        ⟨argInferFuel, hArgValue⟩
                      intro index inputTyp hSource
                      simp only [bodyBindings, CompilerBindings.get, NatBindings.get] at hSource ⊢
                      split at hSource <;> simp_all [entryFits])
                    hBody
                  simpa [eval.eq_4, hFnEval, hArgEval, bodyBindings] using
                    ih (body.apply .only) bodyBindings bodyFuel typ hBodyTarget

/-- A successfully inferred type makes the executable term safe at that type. -/
theorem main (fuel : Nat) (typ : Typ)
    (hInfer : trm.infer bindings fuel = .yield (some typ)) :
    safety trm bindings typ := by
  intro evalFuel
  have safe := inferEvalSafety trm bindings fuel typ hInfer evalFuel
  cases result : trm.eval bindings evalFuel <;> (try cases ‹Option ExeVal›) <;> (try cases ‹ExeVal›) <;>
    simp_all
  obtain ⟨valueFuel, typed⟩ := safe
  exact ⟨valueFuel, by rw [typed]⟩

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
