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
def infer [env: @CompilerEnv I] (self : Trm I) : RecOption (Valid (Typ I)) -- TODO: remove this, not possible in subtyping
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val (.primitive _) => .yield (some .primitive)
    | .val (.fn body tIn) =>
      let index := env.typeRefs.save tIn
      ((body index).infer fuel).map (fun out => out.map (fun tOut => .fn tIn tOut))
    | .apply fn arg =>
      match fn.infer fuel, arg.infer fuel with
      | .yield (some (.fn tIn tOut)), .yield (some argTyp) =>
        if argTyp ≤ tIn then .yield (some tOut) else .yield none
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none
    | .ref i => .yield (some (env.typeRefs.load i))

/-- Inference that succeeds with smaller fuel succeeds with the same type at larger fuel. -/
theorem termInferMonotone [env : @CompilerEnv I]
    (trm : Trm I) :
    trm.infer.Monotone := by
  intro less more result hFuel hInfer
  induction less using Nat.strongRecOn generalizing trm more result with
  | ind fromFuel ih =>
    cases fromFuel with
    | zero =>
      cases trm <;> simp [AST.Trm.infer] at hInfer
    | succ fuel =>
      cases more with
      | zero => cases hFuel
      | succ toFuel =>
        have hFuelTail : fuel <= toFuel := Nat.le_of_succ_le_succ hFuel
        cases trm with
        | val value =>
          cases value with
          | primitive repr => simpa [AST.Trm.infer] using hInfer
          | fn body tIn =>
            cases hBody : (body (env.typeRefs.save tIn)).infer fuel with
            | outOfFuel => simp [AST.Trm.infer, hBody, Outcome.map] at hInfer
            | yield bodyResult =>
              have hBodyTop := ih fuel (Nat.lt_succ_self fuel) (body (env.typeRefs.save tIn)) toFuel bodyResult hFuelTail hBody
              simpa [AST.Trm.infer, Outcome.map, hBody, hBodyTop] using hInfer
        | apply fnTerm arg =>
          cases hFn : fnTerm.infer fuel with
          | outOfFuel => simp [AST.Trm.infer, hFn] at hInfer
          | yield fnResult =>
            cases hArg : arg.infer fuel with
            | outOfFuel => simp [AST.Trm.infer, hFn, hArg] at hInfer
            | yield argResult =>
              have hFnTop := ih fuel (Nat.lt_succ_self fuel) fnTerm toFuel fnResult hFuelTail hFn
              have hArgTop := ih fuel (Nat.lt_succ_self fuel) arg toFuel argResult hFuelTail hArg
              simpa [AST.Trm.infer, hFn, hArg, hFnTop, hArgTop] using hInfer
        | ref id =>
          simpa [AST.Trm.infer] using hInfer

/-- Value inference monotonicity follows from term inference monotonicity. -/
theorem valueInferMonotone [env : @CompilerEnv I]
    (value : AST.Val I) :
    (AST.Trm.val value).infer.Monotone :=
  termInferMonotone (AST.Trm.val value)

end AST.Trm

class ProvingEnv extends (@RuntimeEnv I), (@CompilerEnv I) where
  refSafety : -- consistency between valRefs and typRefs, runtime variable of value can always inhabit compiletime variable of type with the same name
    ∀ (id : I.Index),
        (AST.Trm.val (valueRefs.load id).1).infer.isDecidable (fun typ =>
          typ <= typeRefs.load id
        )
  bindInfer : -- fn body applied on UID of a value can always inhabit the same type of the same fn body applied on UID of the type of that value
    ∀ (body : I.Index -> AST.Trm I) (v : AST.Val I) (fuel : Nat),
      (AST.Trm.val v).infer.isDecidable (fun tIn =>
        (body (typeRefs.save tIn)).infer fuel =
          (body (valueRefs.save { val := v, property := canEvalAny v })).infer fuel
      )
-- TODO: can these be corollaries of a cross-FBound axiom? Namely:
-- - [x] body is a pure function, `(typeRefs.save tIn) = (valueRefs.save { val := v, property := canEvalAny v })` can be inferred if save requires an AST to generate UID
-- - [ ] (same id <-> same term), immutable binding (1 id only refers to 1 type/value) |- mappings in valueRefs & typeRefs are always compatible
--   - TODO: how to make it more obvious?
--     -- By making typeRefs stronger: saving a term into typeRefs will get a UID, it automatically implies that the same UID in valueRefs automatically evaluates to the same type.
--   - [by making a dual UID hashtable UID -> (Option Typ, Option Tr] -- TODO: not necessary, remove

-- typeRefs only accepts well-formed AST that is guaranteed to compile, so

variable [env : @ProvingEnv I]

def Safety : Prop := -- TODO: this conjecture shouldn't be too long
  ∀ (trm : AST.Trm I) (typ : AST.Typ I) (fuel : Nat),
  ∀ (_: (trm.infer fuel) = Outcome.yield (.some typ)),
  trm.eval.isSemiDecidable ( fun vv =>
    RecOption.isDecidable (AST.Trm.val vv).infer (fun t2 => t2 <= typ)
  )

namespace Safety

def proof : @Safety I env := by
  intro trm typ fuel hInfer runtimeFuel
  induction runtimeFuel generalizing trm typ fuel with
  | zero => rfl
  | succ runtimeFuel ih =>
    cases fuel with
    | zero =>
      cases trm <;> simp [AST.Trm.infer] at hInfer
    | succ fuel =>
      cases trm with
      | val value =>
        simp [AST.Trm.eval]
        exact Exists.intro (fuel + 1) (by
          simpa [hInfer] using (show typ <= typ from rfl))
      | ref id =>
        simp [AST.Trm.eval]
        rcases ProvingEnv.refSafety id with ⟨refFuel, hRef⟩
        refine ⟨refFuel, ?_⟩
        simp [AST.Trm.infer] at hInfer
        simpa [hInfer] using hRef
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
                    have hFnSafe := ih fnTerm (.fn tIn typ) fuel hFn
                    have hArgSafe := ih arg argTyp fuel hArg
                    cases hFnEval : fnTerm.eval runtimeFuel with
                    | outOfFuel => simp [AST.Trm.eval, hFnEval]
                    | yield fnEvalResult =>
                      rw [hFnEval] at hFnSafe
                      cases fnEvalResult with
                      | none => cases hFnSafe
                      | some fnValue =>
                        cases fnValue with
                        | primitive repr =>
                          rcases hFnSafe with ⟨fnFuel, hFnSafe⟩
                          cases fnFuel with
                          | zero => simp [AST.Trm.infer] at hFnSafe
                          | succ fnFuel =>
                            simp [AST.Trm.infer] at hFnSafe
                            change AST.Typ.primitive = AST.Typ.fn tIn typ at hFnSafe
                            cases hFnSafe
                        | fn body runtimeTIn =>
                          rcases hFnSafe with ⟨fnFuel, hFnSafe⟩
                          cases fnFuel with
                          | zero => simp [AST.Trm.infer] at hFnSafe
                          | succ bodyFuel =>
                            simp [AST.Trm.infer] at hFnSafe
                            cases hBodyCompile : (body (env.typeRefs.save runtimeTIn)).infer bodyFuel with
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
                                change AST.Typ.fn runtimeTIn bodyTyp = AST.Typ.fn tIn typ at hFnSafe
                                cases hFnSafe
                                cases hArgEval : arg.eval runtimeFuel with
                                | outOfFuel => simp [AST.Trm.eval, hFnEval, hArgEval]
                                | yield argEvalResult =>
                                  rw [hArgEval] at hArgSafe
                                  cases argEvalResult with
                                  | none => cases hArgSafe
                                  | some input =>
                                    let inputIndex := env.valueRefs.save { val := input, property := env.canEvalAny input }
                                    rcases hArgSafe with ⟨inputFuel, hArgSafe⟩
                                    match hInputInfer : (AST.Trm.val input).infer inputFuel with
                                    | .yield (some inputTyp) =>
                                        simp [hInputInfer] at hArgSafe
                                        change inputTyp = argTyp at hArgSafe
                                        change argTyp = tIn at hArgLe
                                        have hBodySafe := ih (body inputIndex) typ bodyFuel (by
                                          rcases ProvingEnv.bindInfer body input bodyFuel with ⟨bindFuel, hBind⟩
                                          match hBindInput : (AST.Trm.val input).infer bindFuel with
                                          | .yield (some bindTyp) =>
                                              simp [hBindInput] at hBind
                                              have hBindTop := AST.Trm.valueInferMonotone input bindFuel (bindFuel + inputFuel) (some bindTyp) (Nat.le_add_right bindFuel inputFuel) hBindInput
                                              have hInputTop := AST.Trm.valueInferMonotone input inputFuel (bindFuel + inputFuel) (some inputTyp) (Nat.le_add_left inputFuel bindFuel) hInputInfer
                                              rw [← hBind]
                                              simpa [Option.some.inj (Outcome.yield.inj (hBindTop.symm.trans hInputTop)), hArgSafe, hArgLe] using hBodyCompile
                                          | .outOfFuel
                                          | .yield none => simp [hBindInput] at hBind
                                        )
                                        cases hBodyEval : (body inputIndex).eval runtimeFuel with
                                        | outOfFuel => simp [AST.Trm.eval, hFnEval, hArgEval, hBodyEval, inputIndex]
                                        | yield bodyEvalResult =>
                                          rw [hBodyEval] at hBodySafe
                                          cases bodyEvalResult with
                                          | none => cases hBodySafe
                                          | some output =>
                                            simp [AST.Trm.eval, hFnEval, hArgEval, hBodyEval, inputIndex]
                                            exact hBodySafe
                                    | .outOfFuel
                                    | .yield none => simp [hInputInfer] at hArgSafe
                  case neg =>
                    rw [hFn, hArg] at hInfer
                    simp [hArgLe] at hInfer

end Safety

end
end STLC

end Lp2lc.Active
