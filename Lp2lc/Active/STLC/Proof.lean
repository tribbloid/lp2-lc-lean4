
import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util
import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active

namespace STLC
open Lp2lc.Active.Util

/-
this file proof an alternative theorem for STLC soundness:

term can be inferred to type using some fuel, evaluating it must leads to either a variable that can be inferred to a lesser type with some (less?) fuel or loop.

Obviously inferring type is not alway available in more complex type system, but it's a good demo for recursive proving
-/

section variable {I : Free}

namespace AST.Trm

/-- Inference that succeeds with smaller fuel succeeds with the same type at larger fuel. -/
theorem termEvalMonotone [env : @RuntimeEnv I]
    (trm : Trm I) :
    trm.eval.Monotone := by
  intro less more result hFuel hEval
  induction less using Nat.strongRecOn generalizing trm more result with
  | ind fromFuel ih =>
    cases fromFuel with
    | zero =>
      cases trm <;> simp [AST.Trm.eval] at hEval
    | succ fuel =>
      cases more with
      | zero => cases hFuel
      | succ toFuel =>
        have hFuelTail : fuel <= toFuel := Nat.le_of_succ_le_succ hFuel
        cases trm with
        | val value =>
          simpa [AST.Trm.eval] using hEval
        | apply fnTerm arg =>
          cases hFn : fnTerm.eval fuel with
          | outOfFuel => simp [AST.Trm.eval, hFn] at hEval
          | yield fnResult =>
            have hFnTop := ih fuel (Nat.lt_succ_self fuel) fnTerm toFuel fnResult hFuelTail hFn
            cases hArg : arg.eval fuel with
            | outOfFuel => simp [AST.Trm.eval, hFn, hArg] at hEval
            | yield argResult =>
              have hArgTop := ih fuel (Nat.lt_succ_self fuel) arg toFuel argResult hFuelTail hArg
              cases fnResult with
              | none =>
                simpa [AST.Trm.eval, hFn, hArg, hFnTop, hArgTop] using hEval
              | some fnValue =>
                cases fnValue with
                | primitive repr =>
                  simpa [AST.Trm.eval, hFn, hArg, hFnTop, hArgTop] using hEval
                | fn body tIn =>
                  cases argResult with
                  | none =>
                    simpa [AST.Trm.eval, hFn, hArg, hFnTop, hArgTop] using hEval
                  | some input =>
                    cases hBody :
                        (body (env.valueRefs.save { val := input, property := env.canEvalAny input })).eval fuel with
                    | outOfFuel =>
                      simp [AST.Trm.eval, hFn, hArg, hBody] at hEval
                    | yield bodyResult =>
                      have hBodyTop :=
                        ih fuel (Nat.lt_succ_self fuel)
                          (body (env.valueRefs.save { val := input, property := env.canEvalAny input }))
                          toFuel bodyResult hFuelTail hBody
                      simpa [AST.Trm.eval, hFn, hArg, hFnTop, hArgTop, hBody, hBodyTop] using hEval
        | ref id =>
          simpa [AST.Trm.eval] using hEval

end AST.Trm


/-- States that semantic typing of a closed term entails operational safety. -/
def Adequacy : Prop :=
  ∀ (term : AST.Trm I) (postcondition : Condition I),
    term.WeakestPre postcondition → term.IsSafe

namespace Adequacy

def proof : @Adequacy I := by
  intro term postcondition weakest fuel runtimeEnv
  specialize weakest fuel
  cases evalResult : term.eval fuel with
  | yield value =>
    cases value with
    | none =>
      simp [AST.Trm.recCanSatisfy, Outcome.map, Outcome.getOrElse, evalResult] at weakest
    | some value =>
      simp [AST.Trm.recCanSatisfy, Outcome.map, Outcome.getOrElse, evalResult]
  | outOfFuel =>
    simp [AST.Trm.recCanSatisfy, Outcome.map, Outcome.getOrElse, evalResult]

end Adequacy
end
