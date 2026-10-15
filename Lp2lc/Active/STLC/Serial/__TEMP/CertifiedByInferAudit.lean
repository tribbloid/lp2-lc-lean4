import «Lp2lc».Active.STLC.Serial.__Eval_certifiedByInfer
import «Lp2lc».Active.STLC.Serial.Eval
import Batteries.Tactic.GeneralizeProofs

namespace Lp2lc.Active.STLC.AST.CertifiedByInferAudit

open Lp2lc.Active.Util

-- Inspect the private recursive implementation without exposing it as a public API.
open Lean Elab Term in
elab "certifiedEvalPrivate" : term => do
  let target := `Lp2lc.Active.STLC.AST.CertifiedByInfer.evalInternal
  let some (internal, _) := (← getEnv).constants.toList.find?
      (λ entry => privateToUserName? entry.1 == some target)
    | throwError "Missing private evaluator declaration {target}"
  return mkConst internal

private abbrev evalCore := certifiedEvalPrivate

open Lean Elab Tactic Term in
elab "unfoldCertifiedEval" : tactic => do
  let core ← Tactic.elabTerm (← `(certifiedEvalPrivate)) none
  let .const name _ := core | throwError "Expected the private evaluator constant"
  evalTactic (← `(tactic| unfold evalCore $(mkIdent name)))

private theorem outcomeAgreement {n} (trm : Trm n) (bindings : ExeBindings)
    (condition : Typ → Prop) (hInfer : (trm.infer bindings).isDecidable condition) (fuel : Nat) :
    (evalCore trm bindings condition hInfer fuel).map (λ result => some result.val) =
      trm.eval bindings fuel := by
  induction fuel generalizing n trm bindings condition with
  | zero => rfl
  | succ fuel ih =>
    cases trm with
    | val value => rfl
    | ref carrier under =>
      unfoldCertifiedEval
      simp only [eval.eq_3]
      split
      · generalize_proofs -abstract hFalse
        exact hFalse.elim
      · simp_all [Rec.Outcome.map]
    | apply fn arg =>
      unfoldCertifiedEval
      dsimp only
      generalize_proofs -abstract fnTyped
      have hFn := ih fn bindings _ fnTyped
      cases hFnEval : evalCore fn bindings _ fnTyped fuel with
      | outOfFuel =>
        have hFnOld : eval fn bindings fuel = .outOfFuel := by
          simpa only [hFnEval, Rec.Outcome.map] using hFn.symm
        change ((evalCore fn bindings _ fnTyped fuel).flatMap _).map _ = _
        rw [hFnEval, eval.eq_4, hFnOld]
        cases eval arg bindings fuel <;> rfl
      | yield fnResult =>
        rcases fnResult with ⟨⟨context, fnValue, captured⟩, fnSafe⟩
        have hFnOld : eval fn bindings fuel = .yield (some (.mk context fnValue captured)) := by
          simpa only [hFnEval, Rec.Outcome.map] using hFn.symm
        change ((evalCore fn bindings _ fnTyped fuel).flatMap _).map _ = _
        rw [hFnEval]
        cases fnValue with
        | lit repr =>
          dsimp only [Rec.Outcome.flatMap]
          generalize_proofs -abstract hFalse
          exact hFalse.elim
        | fn annotation body =>
          dsimp only [Rec.Outcome.flatMap]
          generalize_proofs -abstract argTyped
          have hArg := ih arg bindings _ argTyped
          cases hArgEval : evalCore arg bindings _ argTyped fuel with
          | outOfFuel =>
            have hArgOld : eval arg bindings fuel = .outOfFuel := by
              simpa only [hArgEval, Rec.Outcome.map] using hArg.symm
            change ((evalCore arg bindings _ argTyped fuel).flatMap _).map _ = _
            rw [hArgEval, eval.eq_4, hFnOld, hArgOld]
            rfl
          | yield argResult =>
            have hArgOld : eval arg bindings fuel = .yield (some argResult.val) := by
              simpa only [hArgEval, Rec.Outcome.map] using hArg.symm
            change ((evalCore arg bindings _ argTyped fuel).flatMap _).map _ = _
            rw [hArgEval]
            dsimp only [Rec.Outcome.flatMap]
            generalize_proofs -abstract bodyTyped
            have hBody := ih (body.apply .only) (captured.set (context + 1) argResult.val) condition bodyTyped
            simpa only [Rec.Outcome.flatMap, Rec.Outcome.map, eval.eq_4, hFnOld, hArgOld] using hBody

/-- Erasing the certificate preserves ordinary evaluation after successful inference. -/
theorem agreement {n} (trm : Trm n) (bindings : ExeBindings) (fuel inferFuel : Nat)
    (typ : Typ) (hInfer : trm.infer bindings inferFuel = .yield (some typ)) :
    (trm.eval_certified bindings hInfer fuel).map (λ payload => some payload.val) =
      trm.eval bindings fuel := by
  exact outcomeAgreement trm bindings _ ⟨inferFuel, by simp only [hInfer]; rfl⟩ fuel

#print axioms eval_certified
#print axioms agreement

end Lp2lc.Active.STLC.AST.CertifiedByInferAudit
