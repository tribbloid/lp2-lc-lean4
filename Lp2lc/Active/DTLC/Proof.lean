import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util
import «Lp2lc».Active.DTLC.DTLCDef

namespace Lp2lc.Active

namespace DTLC

open AST
open Lp2lc.Active.Util
open Lp2lc.Active.Util.Outcome

private theorem compileDefaultForTypeEvalSemi {impl : Impl} [Compiletime.Env impl]
    [Runtime.Env impl] (type : Typ impl) (compileFuel runtimeFuel : Nat) :
    isResultOrOutOfFuel
      ((AST.Trm.compile.compileDefaultForType compileFuel type).eval runtimeFuel) := by
  induction compileFuel generalizing type runtimeFuel with
  | zero =>
      cases runtimeFuel <;> cases type <;>
        simp [AST.Trm.compile.compileDefaultForType, AST.Trm.eval, isResultOrOutOfFuel]
  | succ compileFuel ih =>
      cases runtimeFuel with
      | zero =>
          cases type <;>
            simp [AST.Trm.eval, isResultOrOutOfFuel]
      | succ runtimeFuel =>
          cases type <;>
            simp [AST.Trm.compile.compileDefaultForType, AST.Trm.eval, isResultOrOutOfFuel]

private theorem compileDelayedDefaultEvalSemi {impl : Impl} [Compiletime.Env impl]
    [Runtime.Env impl] (type : Typ impl) (compileFuel runtimeFuel : Nat) :
    isResultOrOutOfFuel
      ((AST.Trm.compile.compileDelayChecked
          (AST.Trm.compile.compileDefaultForType compileFuel type)).eval runtimeFuel) := by
  cases runtimeFuel with
  | zero =>
      simp [AST.Trm.eval, isResultOrOutOfFuel]
  | succ runtimeFuel =>
      cases runtimeFuel with
      | zero =>
          simp [AST.Trm.compile.compileDelayChecked, AST.Trm.eval, isResultOrOutOfFuel]
      | succ runtimeFuel =>
          simpa [AST.Trm.compile.compileDelayChecked, AST.Trm.eval] using
            compileDefaultForTypeEvalSemi (impl := impl) type compileFuel (runtimeFuel + 1)

private theorem compileDelayDefaultSafe {impl : Impl} [Compiletime.Env impl]
    [Runtime.Env impl] (type : Typ impl) (compileFuel runtimeFuel : Nat) :
    (AST.Trm.compile.compileDelayChecked
        (AST.Trm.compile.compileDefaultForType compileFuel type)).IsSafe none runtimeFuel := by
  simp [AST.Trm.IsSafe, compileDelayedDefaultEvalSemi]

private theorem compileDefaultForTypeHintSafe {impl : Impl} [Compiletime.Env impl]
    [Runtime.Env impl] (type : Typ impl) (fuel : Nat) :
    (AST.Trm.compile.compileDefaultForType (fuel + 1) type).IsSafe (some type) (fuel + 2) := by
  cases fuel with
  | zero =>
      cases type <;>
        simp [AST.Trm.IsSafe, AST.Trm.compile.compileDefaultForType, AST.Trm.compile,
          AST.Trm.compile.compileWithType, AST.Trm.compile.compileWithTypeFuel,
          AST.Trm.compile.compileWithTypeFuel.eq_1, AST.Trm.compile.compileWithTypeFuel.eq_2,
          AST.Trm.compile.compileWithTypeFuel.eq_4, AST.Trm.compile.compileWithTypeFuel.eq_6,
          AST.Trm.compile.compileTypeCompatible,
          AST.Trm.compile.compileValueCompatible, AST.Trm.eval,
          isResult]
  | succ fuel =>
      cases type <;>
        simp [AST.Trm.IsSafe, AST.Trm.compile.compileDefaultForType, AST.Trm.compile,
          AST.Trm.compile.compileWithType, AST.Trm.compile.compileWithTypeFuel,
          AST.Trm.compile.compileWithTypeFuel.eq_1, AST.Trm.compile.compileWithTypeFuel.eq_2,
          AST.Trm.compile.compileWithTypeFuel.eq_4, AST.Trm.compile.compileWithTypeFuel.eq_6,
          AST.Trm.compile.compileTypeCompatible,
          AST.Trm.compile.compileValueCompatible, AST.Trm.eval,
          isResult]

private theorem compileTypeHintedSafe {impl : Impl} [Compiletime.Env impl]
    [Runtime.Env impl] (self : Trm impl) (hint : Typ impl) (fuel : Nat) :
    match AST.Trm.compile.compileWithTypeFuel fuel none (Trm.typeHinted self hint) with
    | .result (program, _) => program.IsSafe (some hint) fuel
    | _ => True := by
  cases fuel with
  | zero => simp [AST.Trm.compile.compileWithTypeFuel.eq_1]
  | succ fuel =>
      cases fuel with
      | zero =>
          change
            match AST.Trm.compile.compileWithTypeFuel (Nat.succ 0) none
                (Trm.typeHinted self hint) with
            | .result (program, _) => program.IsSafe (some hint) (Nat.succ 0)
            | _ => True
          cases self <;>
            simp [AST.Trm.compile.compileWithTypeFuel.eq_1,
              AST.Trm.compile.compileWithTypeFuel.eq_2,
              AST.Trm.compile.compileWithTypeFuel.eq_3]
      | succ fuel =>
          change
            match AST.Trm.compile.compileWithTypeFuel (Nat.succ (fuel + 1)) none
                (Trm.typeHinted self hint) with
            | .result (program, _) => program.IsSafe (some hint) (Nat.succ (fuel + 1))
            | _ => True
          cases self with
          | val value =>
              rw [AST.Trm.compile.compileWithTypeFuel.eq_2]
              generalize hSelf :
                AST.Trm.compile.compileWithTypeFuel (fuel + 1) none (Trm.val value) = selfResult
              cases selfResult with
              | result selfPair =>
                  rcases selfPair with ⟨_selfProgram, inferred⟩
                  by_cases hCompat : AST.Trm.compile.compileTypeCompatible inferred hint = true
                  · by_cases hValue :
                        AST.Trm.compile.compileValueCompatible value hint = true
                    · simpa [hCompat, hValue] using
                        compileDefaultForTypeHintSafe (impl := impl) hint fuel
                    · simp [hCompat, hValue]
                  · simp [hCompat]
              | error => simp
              | outOfFuel => simp
          | typeHinted _self _hint =>
              simp only [AST.Trm.compile.compileWithTypeFuel.eq_3]
              generalize hInner :
                AST.Trm.compile.compileWithTypeFuel (fuel + 1) none
                    (Trm.typeHinted _self _hint) = innerResult
              cases innerResult with
              | result innerPair =>
                  rcases innerPair with ⟨_innerProgram, inferred⟩
                  by_cases hCompat :
                      AST.Trm.compile.compileTypeCompatible inferred hint = true
                  · simpa [hCompat] using compileDefaultForTypeHintSafe (impl := impl) hint fuel
                  · simp [hCompat]
              | error => simp
              | outOfFuel => simp
          | apply _fn _arg =>
              simp only [AST.Trm.compile.compileWithTypeFuel.eq_3]
              generalize hInner :
                AST.Trm.compile.compileWithTypeFuel (fuel + 1) none
                    (Trm.apply _fn _arg) = innerResult
              cases innerResult with
              | result innerPair =>
                  rcases innerPair with ⟨_innerProgram, inferred⟩
                  by_cases hCompat :
                      AST.Trm.compile.compileTypeCompatible inferred hint = true
                  · simpa [hCompat] using compileDefaultForTypeHintSafe (impl := impl) hint fuel
                  · simp [hCompat]
              | error => simp
              | outOfFuel => simp
          | ref _refValue =>
              simp only [AST.Trm.compile.compileWithTypeFuel.eq_3,
                AST.Trm.compile.compileWithTypeFuel.eq_8]
              by_cases hCompat : AST.Trm.compile.compileTypeCompatible Typ.top hint = true
              · simpa [hCompat] using compileDefaultForTypeHintSafe (impl := impl) hint fuel
              · simp [hCompat]

private theorem compileApplySafe {impl : Impl} [Compiletime.Env impl]
    [Runtime.Env impl] (fn arg : Trm impl) (fuel : Nat) :
    match AST.Trm.compile.compileWithTypeFuel fuel none (Trm.apply fn arg) with
    | .result (program, _) => program.IsSafe none fuel
    | _ => True := by
  cases fuel with
  | zero => simp [AST.Trm.compile.compileWithTypeFuel.eq_1]
  | succ fuel =>
      change
        match AST.Trm.compile.compileWithTypeFuel (Nat.succ fuel) none (Trm.apply fn arg) with
        | .result (program, _) => program.IsSafe none (Nat.succ fuel)
        | _ => True
      rw [AST.Trm.compile.compileWithTypeFuel.eq_7]
      generalize hFn : AST.Trm.compile.compileWithTypeFuel fuel none fn = fnResult
      generalize hArg : AST.Trm.compile.compileWithTypeFuel fuel none arg = argResult
      cases fnResult with
      | error => cases argResult <;> simp
      | outOfFuel => cases argResult <;> simp
      | result fnPair =>
          cases argResult with
          | error => simp
          | outOfFuel => simp
          | result argPair =>
              rcases fnPair with ⟨_compiledFn, fnType⟩
              rcases argPair with ⟨compiledArg, argType⟩
              cases fnType with
              | primitive => simp
              | top => simp
              | depFn tIn tOut =>
                  by_cases hCompat :
                      AST.Trm.compile.compileTypeCompatible argType tIn = true
                  · simp only [hCompat, ↓reduceIte]
                    let fBound := Compiletime.Env.forTyps (impl := impl)
                    let argRef := fBound.save argType (Compiletime.Env.canSaveAnyTyp argType)
                    cases fn with
                    | typeHinted _self _hint =>
                        exact compileDelayDefaultSafe (impl := impl) (tOut argRef) fuel (fuel + 1)
                    | val value =>
                        cases value with
                        | primitive _repr =>
                            exact compileDelayDefaultSafe (impl := impl) (tOut argRef) fuel (fuel + 1)
                        | primitiveFn body =>
                            cases compiledArg with
                            | typeHinted _self _hint => simp
                            | val argValue =>
                                cases argValue with
                                | primitive repr =>
                                    generalize hBody :
                                      AST.Trm.compile.compileWithTypeFuel fuel none (body repr) =
                                        bodyResult
                                    cases bodyResult with
                                    | result bodyPair =>
                                        rcases bodyPair with ⟨_bodyProgram, resultType⟩
                                        simpa [hBody] using
                                          compileDelayDefaultSafe (impl := impl) resultType fuel
                                            (fuel + 1)
                                    | error => simp [hBody]
                                    | outOfFuel => simp [hBody]
                                | primitiveFn _bodyArg => simp
                                | fn _bodyArg => simp
                            | apply _f _a => simp
                            | ref _refValue => simp
                        | fn body =>
                            generalize hBody :
                              AST.Trm.compile.compileWithTypeFuel fuel (some argType)
                                  (body argRef) = bodyResult
                            cases bodyResult with
                            | result bodyPair =>
                                rcases bodyPair with ⟨_bodyProgram, resultType⟩
                                simpa [hBody, argRef] using
                                  compileDelayDefaultSafe (impl := impl) resultType fuel (fuel + 1)
                            | error => simp [hBody, argRef]
                            | outOfFuel => simp [hBody, argRef]
                    | apply _f _a =>
                        exact compileDelayDefaultSafe (impl := impl) (tOut argRef) fuel (fuel + 1)
                    | ref _refValue =>
                        exact compileDelayDefaultSafe (impl := impl) (tOut argRef) fuel (fuel + 1)
                  · simp [hCompat]

theorem AdequacyLemma {impl : Impl}
    [Compiletime.Env impl] [Runtime.Env impl]
    (src : Trm impl) (fuel : Nat) :
    src.IsAdequate fuel := by
  unfold AST.Trm.IsAdequate
  cases src with
  | typeHinted self hint =>
      unfold AST.Trm.compile AST.Trm.compile.compileWithType
      generalize hResult :
        AST.Trm.compile.compileWithTypeFuel fuel none (Trm.typeHinted self hint) = result
      have hSafe := compileTypeHintedSafe (impl := impl) self hint fuel
      rw [hResult] at hSafe
      cases result with
      | result pair =>
          rcases pair with ⟨program, _inferred⟩
          exact hSafe
      | error => simp
      | outOfFuel => simp
  | val value =>
      cases fuel with
      | zero => simp [AST.Trm.compile, AST.Trm.compile.compileWithType,
          AST.Trm.compile.compileWithTypeFuel.eq_1]
      | succ fuel =>
          cases value <;>
            simp [AST.Trm.compile, AST.Trm.compile.compileWithType,
              AST.Trm.compile.compileWithTypeFuel.eq_4,
              AST.Trm.compile.compileWithTypeFuel.eq_5,
              AST.Trm.compile.compileWithTypeFuel.eq_6,
              AST.Trm.IsSafe, AST.Trm.eval, AST.Trm.typeHint, AST.Trm.TypeView.get,
              AST.Trm.TypeView.eraseRecursively, isResultOrOutOfFuel]
  | apply fn arg =>
      unfold AST.Trm.compile AST.Trm.compile.compileWithType
      generalize hResult :
        AST.Trm.compile.compileWithTypeFuel fuel none (Trm.apply fn arg) = result
      have hSafe := compileApplySafe (impl := impl) fn arg fuel
      rw [hResult] at hSafe
      cases result with
      | result pair =>
          rcases pair with ⟨program, _inferred⟩
          exact hSafe
      | error => simp
      | outOfFuel => simp
  | ref refValue =>
      cases fuel with
      | zero => simp [AST.Trm.compile, AST.Trm.compile.compileWithType,
          AST.Trm.compile.compileWithTypeFuel.eq_1]
      | succ fuel =>
          simp [AST.Trm.compile, AST.Trm.compile.compileWithType,
            AST.Trm.compile.compileWithTypeFuel.eq_8,
            AST.Trm.IsSafe, AST.Trm.eval, AST.Trm.typeHint, AST.Trm.TypeView.get,
            isResultOrOutOfFuel]


end DTLC

end Lp2lc.Active
