import «Lp2lc».Active.STLC.Serial.__Infer

namespace Lp2lc.Active.STLC.AST

open Lp2lc.Active.Util

namespace CertifiedByInfer

/-- An evaluation outcome paired with safety under the existing inference rule.

Successful inference excludes rejection and preserves the type of every returned
value in its captured environment. Evaluation may still exhaust its fuel.
-/
structure Result {n} (trm : Trm n) (bindings : ExeBindings) where
  result : Rec.Outcome (Option ExeValue)
  safe : ∀ inferFuel typ, trm.infer bindings inferFuel = .yield (some typ) →
    match result with
    | .outOfFuel => True
    | .yield none => False
    | .yield (some value) =>
      ∃ valueFuel, value.value.asTrm.infer value.captured valueFuel = .yield (some typ)

private theorem inferApplySuccess {fn arg : Trm n}
    {entries : CompilerBindings} {fuel : Nat} {typ : Typ}
    (hInfer : inferInternal (.apply fn arg) entries (fuel + 1) = .yield (some typ)) :
    ∃ input, inferInternal fn entries fuel = .yield (some (.TFn input typ)) ∧
      inferInternal arg entries fuel = .yield (some input) := by
  simp only [inferInternal.eq_5] at hInfer
  repeat split at hInfer
  all_goals simp_all
  all_goals injection hInfer; subst_vars; exact ⟨_, rfl, rfl⟩

private theorem inferFnSuccess {annotation : Typ n} {body : Binder n .trm}
    {entries : CompilerBindings} {fuel : Nat} {typ : Typ}
    (hInfer : inferInternal (.val (.fn annotation body)) entries (fuel + 1) = .yield (some typ)) :
    let input := resolveType annotation
    ∃ output, inferInternal (body.apply .only)
        (entries.set (n + 1) (.inr input)) fuel = .yield (some output) ∧
      typ = .TFn input output := by
  simp only [inferInternal.eq_3, Rec.Outcome.map] at hInfer
  repeat split at hInfer
  all_goals simp_all
  all_goals cases ‹Option Typ› <;> simp only [Option.map] at hInfer
  all_goals try cases hInfer
  all_goals exact ⟨_, rfl, rfl⟩

-- Certification derives its inference facts locally, including fuel transport.
private theorem inferMonotone (trm : Trm n) (bindings : CompilerBindings) :
    (trm.inferInternal bindings).Monotone := by
  intro less more result hFuel hInfer
  induction less generalizing n trm bindings more result with
  | zero => simp [inferInternal] at hInfer
  | succ fuel ih =>
    cases more <;> try (exact False.elim (Nat.not_succ_le_zero _ hFuel))
    replace hFuel := Nat.le_of_succ_le_succ hFuel
    cases trm <;> try cases ‹Val n›
    all_goals
      simp only [inferInternal.eq_2, inferInternal.eq_3, inferInternal.eq_4, inferInternal.eq_5,
        Rec.Outcome.map] at hInfer ⊢
      repeat split at hInfer
      all_goals simp_all

private def entryFits (entry : Option ValOrTyp) (typ : Typ) : Prop :=
  match entry with
  | none => False
  | some (.inr input) => input = typ
  | some (.inl (.mk _ value captured)) =>
    ∃ fuel, inferInternal value.asTrm (captured.map .inl) fuel = .yield (some typ)

/-- Replacing hypothetical entries by inferable runtime values preserves inference. -/
private theorem inferReplace {trm : Trm n}
    {source target : CompilerBindings} {fuel : Nat} {typ : Typ}
    (hReplace : ∀ index typ, entryFits (source index) typ → entryFits (target index) typ)
    (hInfer : inferInternal trm source fuel = .yield (some typ)) :
    ∃ targetFuel, inferInternal trm target targetFuel = .yield (some typ) := by
  induction fuel generalizing n trm source target typ with
  | zero => simp [inferInternal] at hInfer
  | succ fuel ih =>
    cases trm with
    | val value =>
      cases value with
      | lit repr => exact ⟨1, by simpa only [inferInternal.eq_2] using hInfer⟩
      | fn annotation body =>
        let input := resolveType annotation
        obtain ⟨output, hBody, hType⟩ := inferFnSuccess hInfer
        subst typ
        obtain ⟨bodyFuel, hTarget⟩ := ih (target := target.set (n + 1) (.inr input))
          (by intro index inputTyp; simp only [NatBindings.set, List.lookup]; split <;> simp_all [input]) hBody
        dsimp only [input] at hTarget
        exact ⟨bodyFuel + 1, by simp only [inferInternal.eq_3, hTarget, Rec.Outcome.map]; rfl⟩
    | ref carrier under =>
      simp only [inferInternal.eq_4] at hInfer
      have hFit : entryFits (source under.sourceIndex.down) typ := by
        cases hEntry : source under.sourceIndex.down <;> (try cases ‹ValOrTyp›) <;> (try cases ‹ExeValue›)
        all_goals simp only [hEntry, entryFits, Rec.Outcome.yield.injEq] at hInfer ⊢
        all_goals first | (cases hInfer <;> rfl) | exact ⟨fuel, hInfer⟩ | exact Option.some.inj hInfer
      have hTarget := hReplace under.sourceIndex.down typ hFit
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
      have hFnMore := inferMonotone fn target fnFuel (max fnFuel argFuel) _
        (Nat.le_max_left _ _) hFnTarget
      have hArgMore := inferMonotone arg target argFuel (max fnFuel argFuel) _
        (Nat.le_max_right _ _) hArgTarget
      exact ⟨max fnFuel argFuel + 1, by
        simp only [inferInternal.eq_5, hFnMore, hArgMore]
        exact congrArg Rec.Outcome.yield (ite_eq_left (rfl : input = input))⟩

end CertifiedByInfer

/-- Evaluate with an erased safety proof constructed at every recursive step.

The result contains both the ordinary outcome and its certificate. No typing
witness is needed to run evaluation; `safe` applies to any successful inference
of the original term, with an independent inference fuel budget.
-/
def eval_certified {n} (self : Trm n) (bindings : ExeBindings := .empty) :
    (fuel : Nat) → CertifiedByInfer.Result self bindings := by
  intro fuel
  induction fuel generalizing n self bindings with
  | zero => exact ⟨.outOfFuel, by intros; trivial⟩
  | succ fuel recurse =>
    cases self with
    | val value => exact ⟨.yield (some (.mk n value bindings)),
        by intro inferFuel typ hInfer; exact ⟨inferFuel, hInfer⟩⟩
    | ref carrier under => exact ⟨.yield (bindings under.sourceIndex.down), by
        intro inferFuel typ hInfer
        cases inferFuel with
        | zero => simp [infer, inferInternal] at hInfer
        | succ inferFuel =>
          cases hBinding : bindings under.sourceIndex.down <;> (try cases ‹ExeValue›)
          all_goals simp only [infer, inferInternal.eq_4, NatBindings.getMap, hBinding, Option.map] at hInfer ⊢
          all_goals first | cases hInfer | exact ⟨inferFuel, hInfer⟩⟩
    | apply fn arg =>
      let fnResult := recurse fn bindings
      let argResult := recurse arg bindings
      let result := match fnResult.result, argResult.result with
        | .yield (some (.mk context (.fn _ body) captured)), .yield (some value) =>
          (recurse (body.apply .only) (captured.set (context + 1) value)).result
        | .yield _, .yield _ => .yield none
        | _, _ => .outOfFuel
      refine ⟨result, ?_⟩
      intro inferFuel typ hInfer
      cases inferFuel with
      | zero => simp [infer, inferInternal] at hInfer
      | succ inferFuel =>
        obtain ⟨input, hFn, hArg⟩ := CertifiedByInfer.inferApplySuccess hInfer
        have hFnSafety := fnResult.safe inferFuel (.TFn input typ) hFn
        have hArgSafety := argResult.safe inferFuel input hArg
        cases hFnEval : fnResult.result <;>
          (try cases ‹Option ExeValue›) <;> (try cases ‹ExeValue›)
        all_goals simp [hFnEval] at hFnSafety
        case outOfFuel =>
          cases hArgEval : argResult.result <;> simp [result, hFnEval, hArgEval]
        case yield.some.mk context fnValue captured =>
          obtain ⟨fnFuel, hFnValue⟩ := hFnSafety
          cases fnFuel with
          | zero => simp [infer, inferInternal] at hFnValue
          | succ fnFuel =>
            cases fnValue with
            | lit repr =>
              simp only [Val.asTrm, infer, inferInternal.eq_2, Rec.Outcome.yield.injEq] at hFnValue
              cases Option.some.inj hFnValue
            | fn annotation body =>
              cases hArgEval : argResult.result <;>
                (try cases ‹Option ExeValue›) <;> (try cases ‹ExeValue›)
              all_goals simp [hArgEval] at hArgSafety
              case outOfFuel => simp [result, hFnEval, hArgEval]
              case yield.some.mk argContext argValue argCaptured =>
                obtain ⟨argInferFuel, hArgValue⟩ := hArgSafety
                obtain ⟨fnOutput, hBody, hFnType⟩ := CertifiedByInfer.inferFnSuccess hFnValue
                rcases Pre.AST.TFn.inj hFnType with ⟨hInput, hOutput⟩
                subst fnOutput
                rw [← hInput] at hBody
                let bodyBindings := captured.set (context + 1) (.mk argContext argValue argCaptured)
                obtain ⟨bodyFuel, hBodyTarget⟩ := CertifiedByInfer.inferReplace
                  (target := bodyBindings.map .inl)
                  (by
                    have typedArg : CertifiedByInfer.entryFits
                        (some (.inl (.mk _ argValue argCaptured))) input := ⟨argInferFuel, hArgValue⟩
                    intro index inputTyp hSource
                    simp only [bodyBindings, NatBindings.getMap, NatBindings.set, List.lookup] at hSource ⊢
                    split at hSource <;> simp_all [CertifiedByInfer.entryFits]) hBody
                simpa only [result, hFnEval, hArgEval] using
                  (recurse (body.apply .only) bodyBindings).safe bodyFuel typ hBodyTarget

end Lp2lc.Active.STLC.AST
