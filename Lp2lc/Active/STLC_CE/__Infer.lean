import Std
import «Lp2lc».Active.STLC_CE.Proof

namespace Lp2lc.Active

namespace STLC_CE

open Lp2lc.Active.Util
open Lp2lc.Active.Util.Rec

namespace AST.Trm

/--
Gets the strongest post type bound of a term, or fails.

CE references carry their type in the reification evidence, so inference does
not need a compiler-side [Free.Fixpoint].
-/
def infer {ctx : AST.Ctx} (self : AST.Trm ctx) : RecOption AST.Typ
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val (.primitive _) => .yield (some .primitive)
    | .val (.fn tIn body) =>
      (infer (body .ptop) fuel).map (λ out => out.map (λ tOut => .fn tIn tOut))
    | .apply fn arg =>
      match infer fn fuel, infer arg fuel with
      | .yield (some (.fn tIn tOut)), .yield (some argTyp) =>
        if argTyp ≤ tIn then .yield (some tOut) else .yield none
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none
    | @AST.Trm.ref source _ _ proxy =>
      match proxy with
      | @AST.ProxyTop.ptop _ typ => .yield (some typ)

/-- Inference that succeeds with smaller fuel succeeds with the same type at larger fuel. -/
theorem termInferMonotone {ctx : AST.Ctx}
    (trm : AST.Trm ctx) :
    trm.infer.Monotone := by
  intro less more result hFuel hInfer
  induction less using Nat.strongRecOn generalizing ctx trm more result with
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
          | primitive repr =>
            simpa [AST.Trm.infer] using hInfer
          | fn tIn body =>
            cases hBody : AST.Trm.infer (body .ptop) fuel with
            | outOfFuel => simp [AST.Trm.infer, hBody, Outcome.map] at hInfer
            | yield bodyResult =>
              have hBodyTop := ih fuel (Nat.lt_succ_self fuel) (body .ptop) toFuel bodyResult hFuelTail hBody
              simpa [AST.Trm.infer, Outcome.map, hBody, hBodyTop] using hInfer
        | apply fnTerm arg =>
          cases hFn : AST.Trm.infer fnTerm fuel with
          | outOfFuel => simp [AST.Trm.infer, hFn] at hInfer
          | yield fnResult =>
            cases hArg : AST.Trm.infer arg fuel with
            | outOfFuel => simp [AST.Trm.infer, hFn, hArg] at hInfer
            | yield argResult =>
              have hFnTop := ih fuel (Nat.lt_succ_self fuel) fnTerm toFuel fnResult hFuelTail hFn
              have hArgTop := ih fuel (Nat.lt_succ_self fuel) arg toFuel argResult hFuelTail hArg
              simpa [AST.Trm.infer, hFn, hArg, hFnTop, hArgTop] using hInfer
        | ref top =>
          cases top
          simpa [AST.Trm.infer] using hInfer

/-- Source value inference monotonicity follows from term inference monotonicity. -/
theorem valueInferMonotone {ctx : AST.Ctx}
    (value : AST.Val ctx) :
    (AST.Trm.infer (ctx := ctx) (AST.Trm.val value)).Monotone :=
  termInferMonotone (AST.Trm.val value)

end AST.Trm

namespace AST.Val

/-- Infers a value by viewing it as a value term. -/
def infer {ctx : AST.Ctx} (self : AST.Val ctx) : RecOption AST.Typ :=
  AST.Trm.infer (AST.Trm.val self)

/-- Value validity plus inference to a requested type bound. -/
def CanInhabit {ctx : AST.Ctx} (self : AST.Val ctx) (typ : AST.Typ) : Prop :=
  self.infer.isDecidable (λ inferred => inferred <= typ)

end AST.Val

class ProvingEnv where
  refSafety :
    ∀ {ctx source : AST.Ctx} (rt : RuntimeEnv ctx)
      [inst : AST.ReifyIndex source ctx] (proxy : AST.ProxyTop source),
      let value := RuntimeEnv.lookup rt (AST.ReifyIndex.reify (self := inst) proxy)
      value.2.2.CanInhabit (match proxy with | @AST.ProxyTop.ptop _ typ => typ)

section variable {ctx : AST.Ctx} (rt : RuntimeEnv ctx) [ProvingEnv]


namespace AST.Trm

/-- Value validity plus inference to a requested type bound. -/
def CanInhabit (self : AST.Trm ctx) (typ : AST.Typ) : Prop :=
  self.infer.isDecidable (λ inferred => inferred <= typ)

end AST.Trm

def Safety
    (trm : AST.Trm ctx) (typ : AST.Typ) : Prop :=
  (Trm.eval trm rt).isSemiDecidable (λ value => value.2.2.CanInhabit typ)

def InferAdequacy : Prop :=
  ∀ (trm : AST.Trm ctx) (typ : AST.Typ),
  trm.CanInhabit typ ->
  Safety rt trm typ

namespace InferAdequacy

theorem proof : InferAdequacy rt := by
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
      induction runtimeFuel generalizing ctx rt trm typ fuel with
      | zero => simp [Trm.eval]
      | succ runtimeFuel ih =>
        cases fuel with
        | zero => cases trm <;> simp [AST.Trm.infer] at hInferCombined
        | succ fuel =>
          cases trm with
          | val value =>
            simp [Trm.eval]
            exact ⟨fuel + 1, by
              have hReflexive : typ ≤ typ := rfl
              simpa [AST.Val.infer, hInferCombined] using hReflexive⟩
          | ref top =>
            cases top
            simp [AST.Trm.infer] at hInferCombined
            cases hInferCombined
            simpa [Trm.eval] using (ProvingEnv.refSafety rt (proxy := AST.ProxyTop.ptop))
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
                        have hFnSafe := ih rt fnTerm (.fn tIn typ) fuel hFn
                        have hArgSafe := ih rt arg argTyp fuel hArg
                        simp [Trm.eval]
                        cases hFnEval : Trm.eval fnTerm rt runtimeFuel with
                        | outOfFuel => simp
                        | yield fnEvalResult =>
                          rw [hFnEval] at hFnSafe
                          cases fnEvalResult with
                          | none => cases hFnSafe
                          | some fnPackage =>
                            rcases fnPackage with ⟨savedCtx, savedEnv, fnValue⟩
                            cases fnValue with
                            | primitive repr =>
                              rcases hFnSafe with ⟨fnFuel, hFnValueInfer⟩
                              cases fnFuel with
                              | zero => simp [AST.Val.infer, AST.Trm.infer] at hFnValueInfer
                              | succ fnFuel =>
                                simp [AST.Val.infer, AST.Trm.infer] at hFnValueInfer
                                change AST.Typ.primitive = AST.Typ.fn tIn typ at hFnValueInfer
                                cases hFnValueInfer
                            | fn runtimeTIn body =>
                              rcases hFnSafe with ⟨fnFuel, hFnValueInfer⟩
                              cases fnFuel with
                              | zero => simp [AST.Val.infer, AST.Trm.infer] at hFnValueInfer
                              | succ bodyFuel =>
                                simp [AST.Val.infer, AST.Trm.infer] at hFnValueInfer
                                cases hBodyInfer : (body .ptop).infer bodyFuel with
                                | outOfFuel =>
                                  rw [hBodyInfer] at hFnValueInfer
                                  simp [Outcome.map] at hFnValueInfer
                                | yield bodyResult =>
                                  cases bodyResult with
                                  | none =>
                                    rw [hBodyInfer] at hFnValueInfer
                                    simp [Outcome.map] at hFnValueInfer
                                  | some bodyTyp =>
                                    rw [hBodyInfer] at hFnValueInfer
                                    simp [Outcome.map] at hFnValueInfer
                                    change AST.Typ.fn runtimeTIn bodyTyp = AST.Typ.fn tIn typ at hFnValueInfer
                                    have hRuntimeTIn : runtimeTIn = tIn := (AST.Typ.fn.inj hFnValueInfer).1
                                    have hBodyTyp : bodyTyp = typ := (AST.Typ.fn.inj hFnValueInfer).2
                                    cases hRuntimeTIn
                                    cases hBodyTyp
                                    cases hArgEval : Trm.eval arg rt runtimeFuel with
                                    | outOfFuel => simp
                                    | yield argEvalResult =>
                                      rw [hArgEval] at hArgSafe
                                      cases argEvalResult with
                                      | none => cases hArgSafe
                                      | some inputPackage =>
                                        rcases inputPackage with ⟨inputCtx, inputEnv, inputValue⟩
                                        have hInputSafe : inputValue.CanInhabit tIn := by
                                          have hArgEq : argTyp = tIn := hArgLe
                                          simpa [hArgEq] using hArgSafe
                                        have hBodySafe :=
                                          ih (savedEnv.snoc (typ := tIn) inputEnv inputValue)
                                            (body .ptop) typ bodyFuel hBodyInfer
                                        cases hBodyEval :
                                            Trm.eval (body .ptop)
                                              (savedEnv.snoc (typ := tIn) inputEnv inputValue) runtimeFuel with
                                        | outOfFuel => simp [hBodyEval]
                                        | yield bodyEvalResult =>
                                          rw [hBodyEval] at hBodySafe
                                          cases bodyEvalResult with
                                          | none => cases hBodySafe
                                          | some output =>
                                            simp [hBodyEval]
                                            exact hBodySafe
                      · rw [hFn, hArg] at hInferCombined
                        simp [hArgLe] at hInferCombined

end InferAdequacy

end

end STLC_CE

end Lp2lc.Active
