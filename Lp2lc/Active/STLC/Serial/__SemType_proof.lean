import «Lp2lc».Active.STLC.Serial.__SemType

namespace Lp2lc.Active.STLC.AST.Semantic

open Lp2lc.Active.Util

namespace Fundamental

variable {n} (trm : Trm n) (bindings : ExeBindings)

/-- Evaluation cannot reject, and every returned closure has the requested type. -/
def safety (typ : Typ) : Prop :=
  (trm.eval bindings).isSemiDecidable (λ result => result.isSafe (λ value =>
    ∃ fuel, semType value.value.asTrm value.captured fuel typ))

private def entryFits (entry : Option (CompilerTyp ⊕ ExeVal)) (typ : Typ) : Prop :=
  match entry with
  | none => False
  | some (.inl ⟨_, input, _⟩) => resolveType input = typ
  | some (.inr ⟨_, value, captured⟩) => ∃ fuel, semType value.asTrm captured fuel typ

private theorem checkReplace {trm : Trm n}
    {source target : CompilerBindings} {fuel : Nat} {typ : Typ}
    (hReplace : ∀ index typ, entryFits (source index) typ → entryFits (target index) typ)
    (hType : semType trm source fuel typ) :
    ∃ targetFuel, semType trm target targetFuel typ := by
  induction fuel generalizing n trm source target typ with
  | zero => simp [semType, check, Rec.Outcome.getOrElse] at hType
  | succ fuel ih =>
    cases trm with
    | val value =>
      cases value with
      | lit repr => cases typ <;> exact ⟨1, hType⟩
      | fnPrimitive tOut op => exact ⟨1, hType⟩
      | fn annotation body =>
        cases typ with
        | TLit => exact False.elim hType
        | TFn input output =>
          obtain ⟨hInput, hBody⟩ := hType
          obtain ⟨bodyFuel, hTarget⟩ := ih
            (target := target.set (n + 1) ⟨n, annotation, .empty⟩)
            (by
              intro index inputTyp
              simp only [CompilerBindings.get]
              split <;> first | exact id | exact hReplace index inputTyp) hBody
          exact ⟨bodyFuel + 1, hInput, hTarget⟩
    | ref carrier under =>
      simp only [semType, check, Rec.Outcome.getOrElse] at hType
      have hFit : entryFits (source under.sourceIndex.down) typ := by
        split at hType <;> simp_all [entryFits]
        all_goals first | exact ⟨fuel, hType⟩ | rfl
      have hTarget := hReplace under.sourceIndex.down typ hFit
      unfold entryFits at hTarget
      split at hTarget
      · contradiction
      · exact ⟨1, by simp_all [semType, check, Rec.Outcome.getOrElse] <;> rfl⟩
      · obtain ⟨valueFuel, hValue⟩ := hTarget
        exact ⟨valueFuel + 1, by simp_all [semType, check, Rec.Outcome.getOrElse]⟩
    | apply fn arg =>
      obtain ⟨input, hFn, hArg⟩ := hType
      obtain ⟨fnFuel, hFnTarget⟩ := ih hReplace hFn
      obtain ⟨argFuel, hArgTarget⟩ := ih hReplace hArg
      exact ⟨max fnFuel argFuel + 1, input,
        Monotone.termCheck fn target (Nat.le_max_left _ _) hFnTarget,
        Monotone.termCheck arg target (Nat.le_max_right _ _) hArgTarget⟩

/-- Semantic typing excludes evaluation rejection and preserves the result's type. -/
theorem main (fuel : Nat) (typ : Typ)
    (hType : semType trm bindings fuel typ) : safety trm bindings typ := by
  have checked {n} (term : Trm n) (entries : CompilerBindings) (budget : Nat) (ty : Typ)
      (success : infer term entries budget = .yield (some ty)) : semType term entries budget ty := by
    induction budget generalizing n term entries ty with
    | zero => simp [infer] at success
    | succ budget ih =>
      cases term with
      | val value =>
        cases value with
        | lit repr =>
          simp only [infer.eq_2, Rec.Outcome.yield.injEq] at success
          cases Option.some.inj success
          trivial
        | fn annotation body =>
          simp only [infer.eq_3, Rec.Outcome.map] at success
          repeat split at success
          all_goals simp_all
          all_goals cases ‹Option Typ› <;> simp only [Option.map] at success
          all_goals try cases success
          all_goals exact ⟨rfl, ih _ _ _ ‹_›⟩
        | fnPrimitive tOut op =>
          simp only [infer.eq_6, Rec.Outcome.yield.injEq] at success
          cases Option.some.inj success
          rfl
      | ref carrier under =>
        simp only [infer.eq_4] at success
        cases hEntry : entries under.sourceIndex.down <;>
          (try cases ‹CompilerTyp ⊕ ExeVal›) <;> (try cases ‹CompilerTyp›) <;> (try cases ‹ExeVal›)
        all_goals simp only [hEntry] at success
        all_goals simp only [semType, check, Rec.Outcome.getOrElse, hEntry]
        all_goals first
          | cases success <;> rfl
          | exact ih _ _ _ success
      | apply fn arg =>
        simp only [infer.eq_5] at success
        repeat split at success
        all_goals simp_all
        all_goals injection success; subst_vars
        all_goals exact ⟨_, ih _ _ _ ‹_›, ih _ _ _ ‹_›⟩
  intro evalFuel
  induction evalFuel generalizing n trm bindings fuel typ with
  | zero => trivial
  | succ evalFuel ih =>
    cases fuel with
    | zero => simp [semType, check, Rec.Outcome.getOrElse] at hType
    | succ fuel =>
      cases trm with
      | val value => exact ⟨fuel + 1, hType⟩
      | ref carrier under =>
        cases hBinding : bindings under.sourceIndex.down <;> (try cases ‹ExeVal›)
        all_goals simp only [semType, check, Rec.Outcome.getOrElse,
          CompilerBindings.get, hBinding, Option.map, eval.eq_3] at hType ⊢
        all_goals first | contradiction | exact ⟨fuel, hType⟩
      | apply fn arg =>
        obtain ⟨input, hFn, hArg⟩ := hType
        have hFnSafety := ih fn bindings fuel (.TFn input typ) hFn
        have hArgSafety := ih arg bindings fuel input hArg
        cases hFnEval : eval fn bindings evalFuel <;>
          (try cases ‹Option (Return ExeVal)›) <;>
          (try cases ‹Return ExeVal›) <;> (try cases ‹ExeVal›)
        all_goals simp [hFnEval, Return.isSafe] at hFnSafety
        case outOfFuel =>
          cases eval arg bindings evalFuel <;> simp [eval.eq_4, hFnEval]
        case yield.some.corrupted =>
          cases hArgEval : eval arg bindings evalFuel <;>
            (try cases ‹Option (Return ExeVal)›) <;> (try cases ‹Return ExeVal›) <;>
            simp_all [eval.eq_4, Return.isSafe]
        case yield.some.some.mk context fnValue captured =>
          obtain ⟨fnFuel, hFnValue⟩ := hFnSafety
          cases fnFuel with
          | zero => simp [semType, check, Rec.Outcome.getOrElse] at hFnValue
          | succ fnFuel =>
            cases fnValue with
            | lit repr =>
              simp [Val.asTrm, semType, check, Rec.Outcome.getOrElse] at hFnValue
            | fn annotation body =>
              cases hArgEval : eval arg bindings evalFuel <;>
                (try cases ‹Option (Return ExeVal)›) <;>
                (try cases ‹Return ExeVal›) <;> (try cases ‹ExeVal›)
              all_goals simp [hArgEval, Return.isSafe] at hArgSafety
              case yield.some.corrupted =>
                simp [eval.eq_4, hFnEval, hArgEval, Return.isSafe]
              case outOfFuel => simp [eval.eq_4, hFnEval, hArgEval]
              case yield.some.some.mk argContext argValue argCaptured =>
                obtain ⟨hInput, hBody⟩ := hFnValue
                let bodyBindings := captured.set (context + 1) (.mk argContext argValue argCaptured)
                obtain ⟨bodyFuel, hBodyTarget⟩ := checkReplace (target := bodyBindings)
                  (by
                    intro index inputTyp hSource
                    simp only [bodyBindings, CompilerBindings.get, NatBindings.get] at hSource ⊢
                    split at hSource <;> simp_all [entryFits]) hBody
                simpa [eval.eq_4, hFnEval, hArgEval, bodyBindings] using
                  ih (body.apply .only) bodyBindings bodyFuel typ hBodyTarget
            | fnPrimitive tOut op =>
              rcases hFnValue with ⟨rfl⟩
              cases hArgEval : eval arg bindings evalFuel <;>
                (try cases ‹Option (Return ExeVal)›) <;>
                (try cases ‹Return ExeVal›) <;> (try cases ‹ExeVal›)
              all_goals simp [hArgEval, Return.isSafe] at hArgSafety
              case yield.some.corrupted => simp [eval.eq_4, hFnEval, hArgEval, Return.isSafe]
              case outOfFuel => simp [eval.eq_4, hFnEval, hArgEval]
              case yield.some.some.mk argContext argValue argCaptured =>
                obtain ⟨argFuel, hArgValue⟩ := hArgSafety
                cases argFuel with
                | zero => simp [semType, check, Rec.Outcome.getOrElse] at hArgValue
                | succ argFuel =>
                  cases argValue with
                  | lit repr =>
                    simp only [eval.eq_4, hFnEval, hArgEval]
                    cases hCheck : infer (.val (op repr)) captured evalFuel with
                    | outOfFuel => simp [Rec.Outcome.map]
                    | yield output =>
                      simp only [Rec.Outcome.map]
                      split
                      · rename_i hOutput
                        subst output
                        exact ⟨evalFuel, checked _ _ _ _ hCheck⟩
                      · trivial
                  | fn annotation body => exact False.elim hArgValue
                  | fnPrimitive annotation operation =>
                    cases hArgValue

end Fundamental

end Lp2lc.Active.STLC.AST.Semantic
