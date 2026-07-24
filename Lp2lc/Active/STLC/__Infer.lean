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

section variable {F : Free}

namespace AST.Trm

/--
get the strongest post type bound (post-condition) of a term, or throw an error
-/
def infer [env: @CompilerEnv F] (self : Trm F) : RecOption (Typ F)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val (.primitive _) => .yield (some .primitive)
    | .val (.fn body tIn) =>
      let index := env.typeCtx.save tIn
      ((body index).infer fuel).map (λ out => out.map (λ tOut => .fn tIn tOut))
    | .apply fn arg =>
      match fn.infer fuel, arg.infer fuel with
      | .yield (some (.fn tIn tOut)), .yield (some argTyp) =>
        if argTyp ≤ tIn then .yield (some tOut) else .yield none
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none
    | @AST.Trm.ref _ i => .yield (some (env.typeCtx.load i))

/-- Inference that succeeds with smaller fuel succeeds with the same type at larger fuel. -/
theorem termInferMonotone [env : @CompilerEnv F]
    (trm : Trm F) :
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
            cases hBody : (body (env.typeCtx.save tIn)).infer fuel with
            | outOfFuel => simp [AST.Trm.infer, hBody, Outcome.map] at hInfer
            | yield bodyResult =>
              have hBodyTop := ih fuel (Nat.lt_succ_self fuel) (body (env.typeCtx.save tIn)) toFuel bodyResult hFuelTail hBody
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
theorem valueInferMonotone [env : @CompilerEnv F]
    (value : AST.Val F) :
    (AST.Trm.val value).infer.Monotone :=
  termInferMonotone (AST.Trm.val value)


def CanInhabit (trm : Trm F) (typ : AST.Typ F) [@CompilerEnv F] :=
  trm.infer.isDecidable (λ t2 => t2 <= typ)

end AST.Trm

class ProvingBase extends (@RuntimeEnv F), (@CompilerEnv F)

def Safety [@ProvingBase F] (trm : AST.Trm F) (typ : AST.Typ F) : Prop :=
  trm.eval.isSemiDecidable (λ v => (AST.Trm.val v).CanInhabit typ)

namespace Proof

-- TODO: the following axioms assumes consistent, single-part UID between values and types which is not true: 1 type can refer to multiple values
/-
Some improvements:
- RuntimeEnv UID switching to 2-part `(typeUID, valueUID)`
- refSafety should become introduce a ∀ valueUID.
  - once rigorous shadow compiler is implemented, refSafety become a corrolary of the store of safety proofs
- for function bodies that are identical but for different UID, TODO: how to make them consistent
-/
class ProvingEnv extends ProvingBase where
  refSafety : -- (AKA, all values in FBound are proven) consistency between valueCtx and typeCtx, runtime variable of value can always inhabit compiletime variable of type with the same name
    ∀ (id : F.Index),
        (AST.Trm.val (valueGroup.load id)).CanInhabit (typeGroup.load id) -- notice the similarity of this with the outcome of Safety theorem: it should be an induction, not an axiom. Also the same ID hypothesis is sketchy?
  bindInfer : -- (AKA same input, same output) fn body applied on UID of a value can always inhabit the same type of the same fn body applied on UID of the type of that value
    ∀ (body : F.Index -> AST.Trm F) (v : AST.Val F) (fuel : Nat),
      (AST.Trm.val v).infer.isDecidable (λ tV =>
        let typeUID := typeGroup.save tV
        let valueUID := valueGroup.save v
        (body typeUID).infer fuel = (body valueUID).infer fuel -- both evaluates to closure: computation with reference that are not substituted yet
      )

-- typeCtx only accepts well-formed AST that is guaranteed to compile, so


variable [env : @ProvingEnv F]

def InferAdequacy : Prop :=
  ∀ (trm : AST.Trm F) (typ : AST.Typ F),
  trm.CanInhabit typ ->
  Safety trm typ

theorem proof : @InferAdequacy F env := by
  intro trm typ hInhabit
  rcases hInhabit with ⟨fuel, hInfer⟩
  cases hInferResult : trm.infer fuel with
  | outOfFuel => simp [hInferResult] at hInfer
  | yield inferResult =>
    cases inferResult with
    | none => simp [hInferResult] at hInfer
    | some inferredTyp =>
      simp [hInferResult] at hInfer
      have hInferCombined : trm.infer fuel = .yield (.some typ) := hInfer ▸ hInferResult
      clear hInferResult hInfer
      intro runtimeFuel
      induction runtimeFuel generalizing trm typ fuel with
      | zero => simp [AST.Trm.eval]
      | succ runtimeFuel ih =>
        cases fuel with
        | zero => simp [AST.Trm.infer] at hInferCombined
        | succ fuel =>
          cases trm with
          | val value =>
            simp [AST.Trm.eval]
            exact Exists.intro (fuel + 1) (by
              have hReflexive : typ <= typ := rfl
              simpa [hInferCombined] using hReflexive)
          | ref id =>
            simp [AST.Trm.eval]
            rcases ProvingEnv.refSafety id with ⟨refFuel, hRef⟩
            refine ⟨refFuel, ?_⟩
            simp [AST.Trm.infer] at hInferCombined
            simpa [hInferCombined] using hRef
          | apply fnTerm arg =>
            simp [AST.Trm.infer] at hInferCombined
            cases hFn : fnTerm.infer fuel with
            | outOfFuel => simp [hFn] at hInferCombined
            | yield fnResult =>
              cases fnResult with
              | none =>
                cases hArg : arg.infer fuel with
                | outOfFuel => simp [hFn, hArg] at hInferCombined
                | yield argResult => cases argResult <;> simp [hFn, hArg] at hInferCombined
              | some fnTyp =>
                cases fnTyp with
                | primitive =>
                  cases hArg : arg.infer fuel with
                  | outOfFuel => simp [hFn, hArg] at hInferCombined
                  | yield argResult => cases argResult <;> simp [hFn, hArg] at hInferCombined
                | fn tIn tOut =>
                  cases hArg : arg.infer fuel with
                  | outOfFuel => simp [hFn, hArg] at hInferCombined
                  | yield argResult =>
                    cases argResult with
                    | none => simp [hFn, hArg] at hInferCombined
                    | some argTyp =>
                      by_cases hArgLe : argTyp ≤ tIn
                      · rw [hFn, hArg] at hInferCombined
                        simp [hArgLe] at hInferCombined
                        cases hInferCombined
                        -- after this, tOut = typ and hInferCombined is consumed
                        have hFnSafe := ih fnTerm (.fn tIn typ) fuel hFn
                        have hArgSafe := ih arg argTyp fuel hArg
                        simp [AST.Trm.eval]
                        cases hFnEval : fnTerm.eval runtimeFuel with
                        | outOfFuel => simp
                        | yield fnEvalResult =>
                          rw [hFnEval] at hFnSafe
                          cases fnEvalResult with
                          | none => cases hFnSafe
                          | some fnValue =>
                            have hFnSafe' : (AST.Trm.val fnValue).CanInhabit (.fn tIn typ) := by
                              simpa using hFnSafe
                            rcases hFnSafe' with ⟨fnFuel, hFnValueInfer⟩
                            cases fnFuel with
                             | zero => unfold AST.Trm.infer at hFnValueInfer; simp at hFnValueInfer
                             | succ fnFuel =>
                               cases fnValue with
                               | primitive =>
                                 unfold AST.Trm.infer at hFnValueInfer
                                 change AST.Typ.primitive = (.fn tIn typ : AST.Typ F) at hFnValueInfer
                                 cases hFnValueInfer
                                | fn body runtimeTIn =>
                                   have hInferUnfold :
                                       (AST.Trm.val (AST.Val.fn body runtimeTIn)).infer (fnFuel.succ) =
                                         ((body (env.typeCtx.save runtimeTIn)).infer fnFuel).map
                                           (λ out => out.map (λ tOut => .fn runtimeTIn tOut)) := rfl
                                  rw [hInferUnfold] at hFnValueInfer
                                   cases hBodyCompile :
                                       (body (env.typeGroup.save runtimeTIn)).infer fnFuel with
                                  | outOfFuel =>
                                    rw [hBodyCompile] at hFnValueInfer
                                    simp at hFnValueInfer
                                    cases hFnValueInfer
                                  | yield bodyResult =>
                                    cases bodyResult with
                                    | none =>
                                      rw [hBodyCompile] at hFnValueInfer
                                      simp at hFnValueInfer
                                      cases hFnValueInfer
                                    | some bodyTyp =>
                                      rw [hBodyCompile] at hFnValueInfer
                                      simp at hFnValueInfer
                                      cases hFnValueInfer
                                      cases hArgEval : arg.eval runtimeFuel with
                                      | outOfFuel => simp
                                      | yield argEvalResult =>
                                        rw [hArgEval] at hArgSafe
                                        cases argEvalResult with
                                        | none => cases hArgSafe
                                        | some input =>
                                          have hArgSafe' : (AST.Trm.val input).CanInhabit argTyp := by
                                            simpa using hArgSafe
                                          rcases hArgSafe' with ⟨inputFuel, hInputInfer⟩
                                          cases hInferInputCall : (AST.Trm.val input).infer inputFuel with
                                          | outOfFuel =>
                                            rw [hInferInputCall] at hInputInfer
                                            simp at hInputInfer
                                          | yield inputResult =>
                                            rw [hInferInputCall] at hInputInfer
                                            cases inputResult with
                                            | none => simp at hInputInfer
                                            | some v =>
                                              have hvEq : v = argTyp := hInputInfer
                                              have hInputEq : (AST.Trm.val input).infer inputFuel = .yield (some tIn) := by
                                                calc
                                                  (AST.Trm.val input).infer inputFuel = .yield (some v) := hInferInputCall
                                                  _ = .yield (some tIn) := by
                                                    rw [hvEq, hArgLe]
                                              let inputIndex := env.valueGroup.save input
                                              rcases ProvingEnv.bindInfer body input fnFuel with ⟨bindFuel, hBind⟩
                                              match hBindInput : (AST.Trm.val input).infer bindFuel with
                                              | .yield (some bindTyp) =>
                                                simp [hBindInput] at hBind
                                                have hBindTop := AST.Trm.valueInferMonotone input bindFuel
                                                  (bindFuel + inputFuel) (some bindTyp)
                                                  (Nat.le_add_right bindFuel inputFuel) hBindInput
                                                have hInputTop := AST.Trm.valueInferMonotone input inputFuel
                                                  (bindFuel + inputFuel) (some tIn)
                                                  (Nat.le_add_left inputFuel bindFuel) hInputEq
                                                have h_bind_typ_eq : bindTyp = tIn := by
                                                  apply Option.some.inj
                                                  apply Outcome.yield.inj
                                                  calc
                                                    .yield (some bindTyp) = (AST.Trm.val input).infer (bindFuel + inputFuel) := hBindTop.symm
                                                    _ = .yield (some tIn) := hInputTop
                                                subst h_bind_typ_eq
                                                have hBodyCompile' : (body inputIndex).infer fnFuel = .yield (some typ) := by
                                                  rw [← hBind, hBodyCompile]
                                                have hBodySafe := ih (body inputIndex) typ fnFuel hBodyCompile'
                                                cases hBodyEval : (body inputIndex).eval runtimeFuel with
                                                | outOfFuel => simp [hBodyEval, inputIndex]
                                                | yield bodyEvalResult =>
                                                  rw [hBodyEval] at hBodySafe
                                                  cases bodyEvalResult with
                                                  | none => cases hBodySafe
                                                  | some output =>
                                                    dsimp [inputIndex]
                                                    rw [hBodyEval]
                                                    simpa using hBodySafe
                                              | .outOfFuel
                                              | .yield none => simp [hBindInput] at hBind
                      · rw [hFn, hArg] at hInferCombined
                        simp at hInferCombined
                        simp [hArgLe] at hInferCombined

end Proof

end

end STLC

end Lp2lc.Active
