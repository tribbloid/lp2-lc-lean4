import «Lp2lc».Active.STLC.Serial.__SemType
import «Lp2lc».Active.STLC.Serial.__Infer_proof

namespace Lp2lc.Active.STLC.AST.Semantic

open Lp2lc.Active.Util

/-- The independent expected-type judgement agrees with inference at the same fuel. -/
theorem semTypeIffInfer {n} (trm : Trm n) (bindings : CompilerBindings) (fuel : Nat) (typ : Typ) :
    semType trm bindings fuel typ ↔ infer trm bindings fuel = .yield (some typ) := by
  have someEq (left right : Typ) : (some left : Option Typ) = some right ↔ left = right :=
    ⟨Option.some.inj, congrArg some⟩
  have fnEq (a b c d : Typ) : a.TFn b = c.TFn d ↔ a = c ∧ b = d :=
    (Pre.AST.TFn.injEq a b c d).to_iff
  have noWitness : (∃ _ : Typ, False) ↔ False := ⟨λ ⟨_, h⟩ => h, False.elim⟩
  induction fuel generalizing n trm bindings typ with
  | zero => simp [semType, check, infer, Rec.Outcome.getOrElse]
  | succ fuel ih =>
    cases trm with
    | val value =>
      cases value with
      | lit repr => cases typ <;> simp [someEq, semType, check, infer, Rec.Outcome.getOrElse]
      | fn annotation body =>
        cases typ with
        | TLit =>
          cases result : infer (body.apply .only) (bindings.set (n + 1) ⟨n, annotation, .empty⟩) fuel <;>
            (try cases ‹Option Typ›) <;>
            simp [someEq, semType, check, infer, result, Rec.Outcome.getOrElse, Rec.Outcome.map, Option.map]
        | TFn input output =>
          change (resolveType annotation = input ∧ semType (body.apply .only)
            (bindings.set (n + 1) ⟨n, annotation, .empty⟩) fuel output) ↔ _
          refine (and_congr_right (λ _ => ih _ _ _)).trans ?_
          cases result : infer (body.apply .only) (bindings.set (n + 1) ⟨n, annotation, .empty⟩) fuel <;>
            (try cases ‹Option Typ›) <;>
            simp [someEq, fnEq, infer, result, Rec.Outcome.map, Option.map]
    | ref carrier under =>
      cases entry : bindings under.sourceIndex.down <;>
        (try cases ‹CompilerTyp ⊕ ExeVal›) <;> (try cases ‹CompilerTyp›) <;> (try cases ‹ExeVal›)
      all_goals simp only [semType, check, Rec.Outcome.getOrElse, infer.eq_4, entry]
      all_goals first | exact ih _ _ _ | simp [someEq]
    | apply fn arg =>
      change (∃ input, semType fn bindings fuel (.TFn input typ) ∧ semType arg bindings fuel input) ↔ _
      simp only [ih]
      cases fnResult : infer fn bindings fuel <;> (try cases ‹Option Typ›) <;> (try cases ‹Typ›)
      all_goals cases argResult : infer arg bindings fuel <;> (try cases ‹Option Typ›)
      all_goals simp [someEq, fnEq, noWitness, infer, fnResult, argResult, LE.le]
      constructor
      · rintro ⟨input, ⟨hIn, hOut⟩, hArg⟩
        subst_vars
        exact ite_eq_left (rfl : input = input)
      · intro h
        split at h
        · exact ⟨_, ⟨rfl, Option.some.inj h⟩, ‹_›⟩
        · cases h

namespace Fundamental

variable {n} (trm : Trm n) (bindings : ExeBindings)

/-- Evaluation cannot reject, and every returned closure has the requested type. -/
def safety (typ : Typ) : Prop :=
  (trm.eval bindings).isSemiDecidable (λ result => result.isSafe (λ value =>
    ∃ fuel, semType value.value.asTrm value.captured fuel typ))

/-- Semantic typing excludes evaluation rejection and preserves the result's type. -/
theorem main (fuel : Nat) (typ : Typ)
    (hType : semType trm bindings fuel typ) : safety trm bindings typ := by
  simpa only [safety, semTypeIffInfer] using
    AST.Fundamental.inferEvalSafety trm bindings fuel typ
      ((semTypeIffInfer _ _ _ _).mp hType)

end Fundamental

end Lp2lc.Active.STLC.AST.Semantic
