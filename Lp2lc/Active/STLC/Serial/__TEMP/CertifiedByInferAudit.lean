import «Lp2lc».Active.STLC.Serial.__Eval_certifiedByInfer
import «Lp2lc».Active.STLC.Serial.Eval
import Lean

namespace Lp2lc.Active.STLC.AST.CertifiedByInferAudit

open Lp2lc.Active.Util

-- Inspect the private recursive implementation without exposing it as a public API.
open Lean Elab Term in
elab "certifiedEvalPrivate" name:ident : term => do
  let target := `Lp2lc.Active.STLC.AST.CertifiedByInfer ++ name.getId.eraseMacroScopes
  let some (internal, _) := (← getEnv).constants.toList.find?
      (λ entry => privateToUserName? entry.1 == some target)
    | throwError "Missing private evaluator declaration {target}"
  return mkConst internal

open Lean Elab Tactic Term in
elab "unfoldCertifiedEval" : tactic => do
  let core ← Tactic.elabTerm (← `(certifiedEvalPrivate evalInternal)) none
  let .const name _ := core | throwError "Expected the private evaluator constant"
  evalTactic (← `(tactic| unfold $(mkIdent name)))

private abbrev evalCore := certifiedEvalPrivate evalInternal

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
      cases hBinding : bindings under.sourceIndex.down with
      | none =>
        obtain ⟨inferFuel, hInfer⟩ := hInfer
        cases inferFuel with
        | zero => cases hInfer
        | succ inferFuel =>
          simp [infer, inferInternal.eq_4, NatBindings.getMap, hBinding] at hInfer
      | some value =>
        rcases value with ⟨context, value, captured⟩
        change List.lookup under.sourceIndex.down bindings.entries =
          some (.mk context value captured) at hBinding
        unfold evalCore
        unfoldCertifiedEval
        simp only [eval.eq_3, hBinding]
        split <;> simp_all [Rec.Outcome.map]
    | apply fn arg =>
      let fnCondition := λ (fnTyp : Typ) => ∃ input output, fnTyp = .TFn input output ∧
        (infer arg bindings).isDecidable (λ inferred => inferred = input) ∧ condition output
      have fnTyped := (certifiedEvalPrivate inferFunction) hInfer
      have hFn := ih fn bindings fnCondition fnTyped
      cases hFnEval : evalCore fn bindings fnCondition fnTyped fuel with
      | outOfFuel =>
        have hFnOld : eval fn bindings fuel = .outOfFuel := by
          simpa only [hFnEval, Rec.Outcome.map] using hFn.symm
        change ((evalCore fn bindings fnCondition fnTyped fuel).flatMap _).map _ = _
        rw [hFnEval, eval.eq_4, hFnOld]
        cases eval arg bindings fuel <;> rfl
      | yield fnResult =>
        rcases fnResult with ⟨⟨context, fnValue, captured⟩, fnSafe⟩
        have hFnOld : eval fn bindings fuel = .yield (some (.mk context fnValue captured)) := by
          simpa only [hFnEval, Rec.Outcome.map] using hFn.symm
        cases fnValue with
        | lit repr =>
          obtain ⟨fnFuel, _, hFn, input, output, rfl, _, _⟩ := (certifiedEvalPrivate inferWitness) fnSafe
          cases fnFuel with
          | zero => cases hFn
          | succ fnFuel =>
            simp only [infer, Val.asTrm, inferInternal.eq_2, Rec.Outcome.yield.injEq] at hFn
            cases Option.some.inj hFn
        | fn annotation body =>
          have fnFacts := (certifiedEvalPrivate inferFunctionValue) arg bindings condition
            (by simpa only [fnCondition, Val.asTrm] using fnSafe)
          have hArg := ih arg bindings _ fnFacts.1
          cases hArgEval : evalCore arg bindings _ fnFacts.1 fuel with
          | outOfFuel =>
            have hArgOld : eval arg bindings fuel = .outOfFuel := by
              simpa only [hArgEval, Rec.Outcome.map] using hArg.symm
            change ((evalCore fn bindings fnCondition fnTyped fuel).flatMap _).map _ = _
            rw [hFnEval]
            change ((evalCore arg bindings _ fnFacts.1 fuel).flatMap _).map _ = _
            rw [hArgEval, eval.eq_4, hFnOld, hArgOld]
            rfl
          | yield argResult =>
            have hArgOld : eval arg bindings fuel = .yield (some argResult.val) := by
              simpa only [hArgEval, Rec.Outcome.map] using hArg.symm
            let bodyBindings := captured.set (context + 1) argResult.val
            have bodyTyped := (certifiedEvalPrivate inferBody) fnFacts.2 argResult.property
            have hBody := ih (body.apply .only) bodyBindings condition bodyTyped
            change ((evalCore fn bindings fnCondition fnTyped fuel).flatMap _).map _ = _
            rw [hFnEval]
            change ((evalCore arg bindings _ fnFacts.1 fuel).flatMap _).map _ = _
            rw [hArgEval]
            simpa only [Rec.Outcome.flatMap, Rec.Outcome.map, eval.eq_4, hFnOld, hArgOld] using hBody

/-- Erasing the certificate preserves ordinary evaluation after successful inference. -/
theorem agreement {n} (trm : Trm n) (bindings : ExeBindings) (fuel inferFuel : Nat)
    (typ : Typ) (hInfer : trm.infer bindings inferFuel = .yield (some typ)) :
    (trm.eval_certified bindings hInfer fuel).map (λ payload => some payload.v) =
      trm.eval bindings fuel := by
  let accepted : (trm.infer bindings).isDecidable (λ inferred => inferred = typ) :=
    ⟨inferFuel, by simp only [hInfer]; rfl⟩
  have hAgreement := outcomeAgreement trm bindings (λ inferred => inferred = typ) accepted fuel
  change ((evalCore trm bindings _ accepted fuel).map
    (λ result => (⟨result.val, result.property⟩ : CertifiedByInfer.ResultPayload typ))).map _ = _
  cases hResult : evalCore trm bindings _ accepted fuel <;>
    simpa only [hResult, Rec.Outcome.map] using hAgreement

#print axioms eval_certified
#print axioms agreement

end Lp2lc.Active.STLC.AST.CertifiedByInferAudit
