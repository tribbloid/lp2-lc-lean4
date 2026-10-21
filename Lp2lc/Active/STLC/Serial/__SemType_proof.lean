import «Lp2lc».Active.STLC.Serial.__SemType

namespace Lp2lc.Active.STLC.AST.Semantic

open Lp2lc.Active.Util

namespace Fundamental

variable {n} (trm : Trm n) (bindings : ExeBindings)

/-- Evaluation cannot reject, and every returned closure has the requested type. -/
def safety (typ : Typ) : Prop :=
  (trm.eval bindings).isSemiDecidable (λ result =>
    ∃ fuel, semType result.value.asTrm (result.captured.map .inr) fuel typ)

private def entryFits (entry : Option (CompilerTyp ⊕ ExeVal)) (typ : Typ) : Prop :=
  match entry with
  | none => False
  | some (.inl ⟨_, input, _⟩) => resolveType input = typ
  | some (.inr ⟨_, value, captured⟩) => ∃ fuel, semType value.asTrm (captured.map .inr) fuel typ

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
      | fn annotation body =>
        cases typ with
        | TLit => exact False.elim hType
        | TFn input output =>
          obtain ⟨hInput, hBody⟩ := hType
          obtain ⟨bodyFuel, hTarget⟩ := ih
            (target := target.set (n + 1) ⟨n, .inr annotation, target⟩)
            (by
              intro index inputTyp
              simp only [NatBindings.set, List.lookup]
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
    (hType : semType trm (bindings.map .inr) fuel typ) : safety trm bindings typ := by
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
          NatBindings.getMap, hBinding, Option.map, toCompiler, eval.eq_3] at hType ⊢
        all_goals first | contradiction | exact ⟨fuel, hType⟩
      | apply fn arg =>
        obtain ⟨input, hFn, hArg⟩ := hType
        have hFnSafety := ih fn bindings fuel (.TFn input typ) hFn
        have hArgSafety := ih arg bindings fuel input hArg
        cases hFnEval : eval fn bindings evalFuel <;>
          (try cases ‹Option ExeVal›) <;> (try cases ‹ExeVal›)
        all_goals simp [hFnEval] at hFnSafety
        case outOfFuel =>
          cases eval arg bindings evalFuel <;> simp [eval.eq_4, hFnEval]
        case yield.some.mk context fnValue captured =>
          obtain ⟨fnFuel, hFnValue⟩ := hFnSafety
          cases fnFuel with
          | zero => simp [semType, check, Rec.Outcome.getOrElse] at hFnValue
          | succ fnFuel =>
            cases fnValue with
            | lit repr =>
              simp [Val.asTrm, semType, check, Rec.Outcome.getOrElse] at hFnValue
            | fn annotation body =>
              cases hArgEval : eval arg bindings evalFuel <;>
                (try cases ‹Option ExeVal›) <;> (try cases ‹ExeVal›)
              all_goals simp [hArgEval] at hArgSafety
              case outOfFuel => simp [eval.eq_4, hFnEval, hArgEval]
              case yield.some.mk argContext argValue argCaptured =>
                obtain ⟨hInput, hBody⟩ := hFnValue
                let bodyBindings := captured.set (context + 1) (.mk argContext argValue argCaptured)
                obtain ⟨bodyFuel, hBodyTarget⟩ := checkReplace (target := bodyBindings.map toCompiler)
                  (by
                    intro index inputTyp hSource
                    simp only [bodyBindings, NatBindings.getMap, NatBindings.set, List.lookup] at hSource ⊢
                    split at hSource <;> simp_all [entryFits, toCompiler, NatBindings.map]) hBody
                simpa [eval.eq_4, hFnEval, hArgEval, bodyBindings] using
                  ih (body.apply .only) bodyBindings bodyFuel typ hBodyTarget

end Fundamental

end Lp2lc.Active.STLC.AST.Semantic
