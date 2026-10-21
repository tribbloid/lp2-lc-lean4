import «Lp2lc».Active.STLC.Serial.__SemType

namespace Lp2lc.Active.STLC.AST.Semantic

open Lp2lc.Active.Util

namespace Fundamental

variable {n} (trm : Trm n) (bindings : ExeBindings)

/-- Evaluation cannot reject, and every returned closure has the requested type. -/
def safety (typ : Typ) : Prop :=
  (trm.eval bindings).isSemiDecidable (λ result => result.isSafe (λ value =>
    ∃ fuel, semType value.value.asTrm value.captured fuel typ))

/-- Semantic typing excludes evaluation rejection and preserves the result's type. -/
theorem main (fuel : Nat) (typ : Typ)
    (hType : semType trm bindings fuel typ) : safety trm bindings typ := by
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
          (try cases ‹Option (Rec.Return ExeVal)›) <;>
          (try cases ‹Rec.Return ExeVal›) <;> (try cases ‹ExeVal›)
        all_goals simp [hFnEval, Rec.Return.isSafe] at hFnSafety
        case outOfFuel =>
          cases eval arg bindings evalFuel <;> simp [eval.eq_4, hFnEval]
        case yield.some.corrupted =>
          cases hArgEval : eval arg bindings evalFuel <;>
            (try cases ‹Option (Rec.Return ExeVal)›) <;> (try cases ‹Rec.Return ExeVal›) <;>
            simp_all [eval.eq_4, Rec.Return.isSafe]
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
                (try cases ‹Option (Rec.Return ExeVal)›) <;>
                (try cases ‹Rec.Return ExeVal›) <;> (try cases ‹ExeVal›)
              all_goals simp [hArgEval, Rec.Return.isSafe] at hArgSafety
              case yield.some.corrupted =>
                simp [eval.eq_4, hFnEval, hArgEval, Rec.Return.isSafe]
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

end Fundamental

end Lp2lc.Active.STLC.AST.Semantic
