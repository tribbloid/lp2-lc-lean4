import «Lp2lc».Active.STLC.Serial.__Eval_certifiedByInfer
import «Lp2lc».Active.STLC.Serial.__Infer_proof

namespace Lp2lc.Active.STLC.AST.CertifiedByInferAudit

open Lp2lc.Active.Util

private theorem outcomeAgreement {n} (trm : Trm n) (bindings : ExeBindings) (fuel : Nat) :
    (trm.eval_certified bindings fuel).map (λ payload => some payload.v) =
      (match trm.eval bindings fuel with
      | .yield none => .outOfFuel
      | outcome => outcome) := by
  induction fuel generalizing n trm bindings with
  | zero => rfl
  | succ fuel ih =>
    cases trm with
    | val value => rfl
    | ref carrier under =>
      cases hBinding : bindings under.sourceIndex.down with
      | none =>
        change List.lookup under.sourceIndex.down bindings.entries = none at hBinding
        simp only [eval_certified, eval.eq_3, hBinding]
        split <;> simp_all [Rec.Outcome.map]
      | some value =>
        rcases value with ⟨context, value, captured⟩
        change List.lookup under.sourceIndex.down bindings.entries =
          some (.mk context value captured) at hBinding
        simp only [eval_certified, eval.eq_3, hBinding]
        split <;> simp_all [Rec.Outcome.map]
    | apply fn arg =>
      have hFn := ih fn bindings
      have hArg := ih arg bindings
      cases hFnEval : eval_certified fn bindings fuel with
      | outOfFuel =>
        have hResult : (eval_certified (.apply fn arg) bindings (fuel + 1)).map
            (λ payload => some payload.v) = .outOfFuel := by
          change ((eval_certified fn bindings fuel).flatMap _).map _ = _
          rw [hFnEval]
          rfl
        rw [hResult, eval.eq_4]
        cases hFnOld : eval fn bindings fuel <;> (try cases ‹Option ExeValue›) <;>
          cases hArgOld : eval arg bindings fuel <;> (try cases ‹Option ExeValue›) <;>
          simp_all [Rec.Outcome.map]
      | yield fnResult =>
        cases hArgEval : eval_certified arg bindings fuel with
        | outOfFuel =>
          have hResult : (eval_certified (.apply fn arg) bindings (fuel + 1)).map
              (λ payload => some payload.v) = .outOfFuel := by
            change ((eval_certified fn bindings fuel).flatMap _).map _ = _
            rw [hFnEval]
            change ((eval_certified arg bindings fuel).flatMap _).map _ = _
            rw [hArgEval]
            rfl
          rw [hResult, eval.eq_4]
          cases hFnOld : eval fn bindings fuel <;> (try cases ‹Option ExeValue›) <;>
            cases hArgOld : eval arg bindings fuel <;> (try cases ‹Option ExeValue›) <;>
            simp_all [Rec.Outcome.map]
        | yield argResult =>
          rcases fnResult with ⟨⟨context, fnValue, captured⟩, fnSafe⟩
          rcases argResult with ⟨⟨argContext, argValue, argCaptured⟩, argSafe⟩
          simp only [hFnEval, hArgEval, Rec.Outcome.map] at hFn hArg
          cases hFnOld : eval fn bindings fuel <;> (try cases ‹Option ExeValue›)
          all_goals simp_all
          cases hArgOld : eval arg bindings fuel <;> (try cases ‹Option ExeValue›)
          all_goals simp_all
          subst_vars
          change ((eval_certified fn bindings fuel).flatMap _).map _ = _
          rw [hFnEval]
          change ((eval_certified arg bindings fuel).flatMap _).map _ = _
          rw [hArgEval]
          cases fnValue with
          | lit repr =>
            simp [Rec.Outcome.flatMap, Rec.Outcome.map, eval.eq_4, hFnOld, hArgOld]
          | fn annotation body =>
            have hBody := ih (body.apply .only)
              (captured.set (context + 1) (.mk argContext argValue argCaptured))
            cases hBodyEval : eval_certified (body.apply .only)
                (captured.set (context + 1) (.mk argContext argValue argCaptured)) fuel <;>
              simpa only [Rec.Outcome.flatMap, Rec.Outcome.map, hBodyEval, eval.eq_4, hFnOld, hArgOld]
                using hBody

/-- Erasing the certificate preserves ordinary evaluation after successful inference. -/
theorem agreement {n} (trm : Trm n) (bindings : ExeBindings) (fuel inferFuel : Nat)
    (typ : Typ) (hInfer : trm.infer bindings inferFuel = .yield (some typ)) :
    (trm.eval_certified bindings fuel).map (λ payload => some payload.v) =
      trm.eval bindings fuel := by
  have hSafe := Fundamental.inferEvalSafety trm bindings inferFuel typ hInfer fuel
  rw [outcomeAgreement]
  cases hEval : trm.eval bindings fuel <;> (try cases ‹Option ExeValue›) <;> simp_all

#print axioms eval_certified
#print axioms agreement

end Lp2lc.Active.STLC.AST.CertifiedByInferAudit
