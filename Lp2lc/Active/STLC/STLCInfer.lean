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

/--
get the strongest post type bound (post-condition) of a term, or throw an error
-/
def infer [env: @CompilerEnv I] (self : Trm I) : RecOption (Typ I) -- TODO: remove this, not possible in subtyping
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val (.primitive _) => .yield (some .primitive)
    | .val (.fn body tIn) =>
      let index := env.typRefs.save tIn
      ((body index).infer fuel).map (fun out => out.map (fun tOut => .fn tIn tOut))
    | .apply fn arg =>
      match fn.infer fuel, arg.infer fuel with
      | .yield (some (.fn tIn tOut)), .yield (some argTyp) =>
        if argTyp ≤ tIn then .yield (some tOut) else .yield none
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none
    | .ref i => .yield (some (env.typRefs.load i))

/-- Inference that succeeds with smaller fuel succeeds with the same type at larger fuel. -/
theorem termInferMonotone [env : @CompilerEnv I]
    (trm : Trm I) :
    let self : Rec (Option (Typ I)) := trm.infer
    self.Monotone Option.some := by
  dsimp
  intro fromFuel toFuel typ hFuel hInfer
  induction fromFuel using Nat.strongRecOn generalizing trm toFuel typ with
  | ind fromFuel ih =>
    cases fromFuel with
    | zero =>
      cases trm <;> simp [AST.Trm.infer] at hInfer
    | succ fuel =>
      cases toFuel with
      | zero => cases hFuel
      | succ toFuel =>
        have hFuelTail : fuel <= toFuel := Nat.le_of_succ_le_succ hFuel
        cases trm with
        | val value =>
          cases value with
          | primitive repr =>
            simp [AST.Trm.infer] at hInfer
            subst typ
            simp [AST.Trm.infer]
          | fn body tIn =>
            simp [AST.Trm.infer] at hInfer
            cases hBody : (body (env.typRefs.save tIn)).infer fuel with
            | outOfFuel => simp [hBody, Outcome.map] at hInfer
            | yield bodyResult =>
              cases bodyResult with
              | none => simp [hBody, Outcome.map] at hInfer
              | some bodyTyp =>
                simp [hBody, Outcome.map] at hInfer
                have hBodyTop := ih fuel (Nat.lt_succ_self fuel) (body (env.typRefs.save tIn)) toFuel bodyTyp hFuelTail hBody
                simp [AST.Trm.infer, Outcome.map, hBodyTop, hInfer]
        | apply fnTerm arg =>
          simp [AST.Trm.infer] at hInfer
          cases hFn : fnTerm.infer fuel with
          | outOfFuel => simp [hFn] at hInfer
          | yield fnResult =>
            cases fnResult with
            | none =>
              cases hArg : arg.infer fuel with
              | outOfFuel => simp [hFn, hArg] at hInfer
              | yield argResult => cases argResult <;> simp [hFn, hArg] at hInfer
            | some fnTyp =>
              cases fnTyp with
              | primitive =>
                cases hArg : arg.infer fuel with
                | outOfFuel => simp [hFn, hArg] at hInfer
                | yield argResult => cases argResult <;> simp [hFn, hArg] at hInfer
              | fn tIn tOut =>
                cases hArg : arg.infer fuel with
                | outOfFuel => simp [hFn, hArg] at hInfer
                | yield argResult =>
                  cases argResult with
                  | none => simp [hFn, hArg] at hInfer
                  | some argTyp =>
                    by_cases hArgLe : argTyp <= tIn
                    case pos =>
                      simp [hFn, hArg, hArgLe] at hInfer
                      have hFnTop := ih fuel (Nat.lt_succ_self fuel) fnTerm toFuel (.fn tIn tOut) hFuelTail hFn
                      have hArgTop := ih fuel (Nat.lt_succ_self fuel) arg toFuel argTyp hFuelTail hArg
                      simp [AST.Trm.infer, hFnTop, hArgTop, hArgLe, hInfer]
                    case neg =>
                      simp [hFn, hArg, hArgLe] at hInfer
        | ref id =>
          simp [AST.Trm.infer] at hInfer
          subst typ
          simp [AST.Trm.infer]

/-- Value inference monotonicity follows from term inference monotonicity. -/
theorem valueInferMonotone [env : @CompilerEnv I]
    (value : AST.Val I) (fromFuel toFuel : Nat) (typ : AST.Typ I) :
    fromFuel <= toFuel ->
    (AST.Trm.val value).infer fromFuel = .yield (some typ) ->
    exists typ2, (AST.Trm.val value).infer toFuel = .yield (some typ2) /\ typ2 <= typ :=
  fun hFuel hInfer =>
    Exists.intro typ (And.intro (termInferMonotone (AST.Trm.val value) fromFuel toFuel typ hFuel hInfer) rfl)

end AST.Trm


class ProvingEnv extends (@RuntimeEnv I), (@CompilerEnv I) where
  refSafety :
    forall (id : I.Index) (fuel : Nat),
      exists typ, (AST.Trm.val (valueRefs.load id).1).infer fuel = .yield (some typ) /\ typ <= typRefs.load id
  bindInfer :
    forall (body : I.Index -> AST.Trm I) (tIn tOut : AST.Typ I) (input : AST.Val I) (inputFuel bodyFuel : Nat),
      (body (typRefs.save tIn)).infer bodyFuel = .yield (some tOut) ->
      (exists inputTyp, (AST.Trm.val input).infer inputFuel = .yield (some inputTyp) /\ inputTyp <= tIn) ->
      (body (valueRefs.save { val := input, property := canEvalAny input })).infer bodyFuel = .yield (some tOut)

variable [env : @ProvingEnv I]

def Safety : Prop := -- TODO: this conjecture shouldn't be too long
  ∀ (trm : AST.Trm I) (typ : AST.Typ I) (fuel : Nat),
  ∀ (_: (trm.infer fuel) = Outcome.yield (.some typ)),
  trm.eval.isSemiDecidable ( fun vv =>
    match (AST.Trm.val vv).infer fuel with
    | Outcome.yield (.some t2) => t2 <= typ
    | _ => false
  )

namespace Safety

def proof : @Safety I env := by
  intro trm typ fuel hInfer runtimeFuel
  induction fuel using Nat.strongRecOn generalizing trm typ runtimeFuel with
  | ind fuelTop ih =>
    cases fuelTop with
    | zero =>
      cases trm <;> simp [AST.Trm.infer] at hInfer
    | succ fuel =>
      cases trm with
      | val value =>
        cases runtimeFuel with
        | zero => rfl
        | succ runtimeFuel =>
          simpa [AST.Trm.eval, hInfer] using (show typ <= typ from rfl)
      | ref id =>
        cases runtimeFuel with
        | zero => rfl
        | succ runtimeFuel =>
          simp [AST.Trm.eval]
          have hRef := ProvingEnv.refSafety id (fuel + 1)
          cases hRef with
          | intro typ2 hRest =>
            cases hRest with
            | intro hValueInfer hLe =>
              rw [hValueInfer]
              simp [AST.Trm.infer] at hInfer
              simpa [hInfer] using hLe
      | apply fnTerm arg =>
        simp [AST.Trm.infer] at hInfer
        cases hFn : fnTerm.infer fuel with
        | outOfFuel => simp [hFn] at hInfer
        | yield fnResult =>
          cases fnResult with
          | none =>
            cases hArg : arg.infer fuel with
            | outOfFuel => simp [hFn, hArg] at hInfer
            | yield argResult => cases argResult <;> simp [hFn, hArg] at hInfer
          | some fnTyp =>
            cases fnTyp with
            | primitive =>
              cases hArg : arg.infer fuel with
              | outOfFuel => simp [hFn, hArg] at hInfer
              | yield argResult => cases argResult <;> simp [hFn, hArg] at hInfer
            | fn tIn tOut =>
              cases hArg : arg.infer fuel with
              | outOfFuel => simp [hFn, hArg] at hInfer
              | yield argResult =>
                cases argResult with
                | none => simp [hFn, hArg] at hInfer
                | some argTyp =>
                  by_cases hArgLe : argTyp <= tIn
                  case pos =>
                    rw [hFn, hArg] at hInfer
                    simp [hArgLe] at hInfer
                    cases hInfer
                    cases runtimeFuel with
                    | zero => rfl
                    | succ runtimeFuel =>
                      have hFnSafe := ih fuel (Nat.lt_succ_self fuel) fnTerm (.fn tIn typ) hFn runtimeFuel
                      have hArgSafe := ih fuel (Nat.lt_succ_self fuel) arg argTyp hArg runtimeFuel
                      cases hFnEval : fnTerm.eval runtimeFuel with
                      | outOfFuel => simp [AST.Trm.eval, hFnEval]
                      | yield fnEvalResult =>
                        rw [hFnEval] at hFnSafe
                        cases fnEvalResult with
                        | none => cases hFnSafe
                        | some fnValue =>
                          cases fnValue with
                          | primitive repr =>
                            cases fuel with
                            | zero => simp [AST.Trm.infer] at hFnSafe
                            | succ fuelPred =>
                              simp [AST.Trm.infer] at hFnSafe
                              cases hFnSafe
                          | fn body runtimeTIn =>
                            cases fuel with
                            | zero => simp [AST.Trm.infer] at hFnSafe
                            | succ bodyFuel =>
                              simp [AST.Trm.infer] at hFnSafe
                              cases hBodyCompile : (body (env.typRefs.save runtimeTIn)).infer bodyFuel with
                              | outOfFuel =>
                                rw [hBodyCompile] at hFnSafe
                                simp [Outcome.map] at hFnSafe
                              | yield bodyResult =>
                                cases bodyResult with
                                | none =>
                                  rw [hBodyCompile] at hFnSafe
                                  simp [Outcome.map] at hFnSafe
                                | some bodyTyp =>
                                  rw [hBodyCompile] at hFnSafe
                                  simp [Outcome.map] at hFnSafe
                                  cases hFnSafe
                                  cases hArgEval : arg.eval runtimeFuel with
                                  | outOfFuel => simp [AST.Trm.eval, hFnEval, hArgEval]
                                  | yield argEvalResult =>
                                    rw [hArgEval] at hArgSafe
                                    cases argEvalResult with
                                    | none => cases hArgSafe
                                    | some input =>
                                      cases hInputInfer : (AST.Trm.val input).infer (bodyFuel + 1) with
                                      | outOfFuel => simp [hInputInfer] at hArgSafe
                                      | yield inputInferResult =>
                                        cases inputInferResult with
                                        | none => simp [hInputInfer] at hArgSafe
                                        | some inputTyp =>
                                          simp [hInputInfer] at hArgSafe
                                          have hInputLe : inputTyp <= tIn := by
                                            change inputTyp = tIn
                                            change inputTyp = argTyp at hArgSafe
                                            change argTyp = tIn at hArgLe
                                            exact hArgSafe.trans hArgLe
                                          have hInputForBind : exists inputTyp, (AST.Trm.val input).infer (bodyFuel + 1) = .yield (some inputTyp) /\ inputTyp <= tIn := by
                                            exact Exists.intro inputTyp (And.intro hInputInfer hInputLe)
                                          have hBodyRuntimeInfer := ProvingEnv.bindInfer body tIn typ input (bodyFuel + 1) bodyFuel hBodyCompile hInputForBind
                                          have hBodyFuelLt : bodyFuel < bodyFuel + 1 + 1 := Nat.lt_trans (Nat.lt_succ_self bodyFuel) (Nat.lt_succ_self (bodyFuel + 1))
                                          have hBodySafe := ih bodyFuel hBodyFuelLt (body (env.valueRefs.save { val := input, property := env.canEvalAny input })) typ hBodyRuntimeInfer runtimeFuel
                                          cases hBodyEval : (body (env.valueRefs.save { val := input, property := env.canEvalAny input })).eval runtimeFuel with
                                          | outOfFuel => simp [AST.Trm.eval, hFnEval, hArgEval, hBodyEval]
                                          | yield bodyEvalResult =>
                                            rw [hBodyEval] at hBodySafe
                                            cases bodyEvalResult with
                                            | none => cases hBodySafe
                                            | some output =>
                                              cases hOutputInfer : (AST.Trm.val output).infer bodyFuel with
                                              | outOfFuel => simp [hOutputInfer] at hBodySafe
                                              | yield outputInferResult =>
                                                cases outputInferResult with
                                                | none => simp [hOutputInfer] at hBodySafe
                                                | some outputTyp =>
                                                  simp [hOutputInfer] at hBodySafe
                                                  have hOutputFuel := AST.Trm.valueInferMonotone output bodyFuel (bodyFuel + 1 + 1) outputTyp (Nat.le_of_lt hBodyFuelLt) hOutputInfer
                                                  cases hOutputFuel with
                                                  | intro topTyp hOutputFuelRest =>
                                                    cases hOutputFuelRest with
                                                    | intro hTopInfer hTopLe =>
                                                      simp [AST.Trm.eval, hFnEval, hArgEval, hBodyEval]
                                                      rw [hTopInfer]
                                                      have hTopToTyp : topTyp <= typ := by
                                                        change topTyp = typ
                                                        change topTyp = outputTyp at hTopLe
                                                        change outputTyp = typ at hBodySafe
                                                        exact hTopLe.trans hBodySafe
                                                      exact hTopToTyp
                  case neg =>
                    rw [hFn, hArg] at hInfer
                    simp [hArgLe] at hInfer

end Safety

end
end STLC

end Lp2lc.Active
