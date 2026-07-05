import Std
import «Lp2lc».Active.STLC_CE.Proof

namespace Lp2lc.Active

namespace STLC_CE

open Lp2lc.Active.Util

namespace AST.Trm

/--
Gets the strongest post type bound of a term, or fails.

CE references carry their type in the reification evidence, so inference does
not need a compiler-side `FBound`.
-/
def infer {ctx : AST.Ctx} (self : AST.Trm ctx) : RecOption AST.Typ
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val (.primitive _) => .yield (some .primitive)
    | .val (.fn tIn body) =>
      (infer (body .ptop) fuel).map (fun out => out.map (fun tOut => .fn tIn tOut))
    | .apply fn arg =>
      match infer fn fuel, infer arg fuel with
      | .yield (some (.fn tIn tOut)), .yield (some argTyp) =>
        if argTyp ≤ tIn then .yield (some tOut) else .yield none
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none
    | @AST.Trm.ref _ typ _ => .yield (some typ)

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
          simpa [AST.Trm.infer] using hInfer

/-- Source value inference monotonicity follows from term inference monotonicity. -/
theorem valueInferMonotone {ctx : AST.Ctx}
    (value : AST.Val) :
    (AST.Trm.infer (ctx := ctx) (AST.Trm.val value)).Monotone :=
  termInferMonotone (AST.Trm.val value)

end AST.Trm

namespace AST.Val

/-- Infers a value by viewing it as a value term. -/
def infer (self : AST.Val) : RecOption AST.Typ :=
  AST.Trm.infer (ctx := AST.Ctx.empty) (AST.Trm.val self)

/-- Value validity plus inference to a requested type bound. -/
def CanInhabit (self : AST.Val) (typ : AST.Typ) : Prop :=
  self.infer.isDecidable (fun inferred => inferred <= typ)

end AST.Val

def Safety {ctx : AST.Ctx} (env : AST.RuntimeEnv ctx)
    (trm : AST.Trm ctx) (typ : AST.Typ) : Prop :=
  (trm.eval env).isSemiDecidable (fun value => value.CanInhabit typ)

def InferAdequacy : Prop :=
  ∀ {ctx : AST.Ctx} (env : AST.RuntimeEnv ctx),
  (∀ {typ : AST.Typ} (top : AST.ProxyTop ctx typ), (env top).CanInhabit typ) ->
  ∀ (trm : AST.Trm ctx),
  ∀ (typ : AST.Typ) (fuel : Nat),
    trm.infer fuel = Outcome.yield (.some typ) ->
    Safety env trm typ

namespace InferAdequacy

def proof : InferAdequacy := by
  intro ctx env hEnv trm typ fuel hInfer runtimeFuel
  induction runtimeFuel generalizing ctx env hEnv trm typ fuel with
  | zero => rfl
  | succ runtimeFuel ih =>
    cases fuel with
    | zero =>
      cases trm <;> simp [AST.Trm.infer] at hInfer
    | succ fuel =>
      cases trm with
      | val value =>
        cases value with
        | primitive repr =>
          have hPrim : AST.Typ.primitive = typ := by
            simpa [AST.Trm.infer] using hInfer
          simp [AST.Trm.eval]
          exact ⟨fuel + 1, by
            simp [AST.Val.infer, AST.Trm.infer]
            change AST.Typ.primitive = typ
            exact hPrim⟩
        | fn tIn body =>
          have hFnInfer :
              ((body AST.ProxyTop.ptop).infer fuel).map
                (fun out => Option.map (fun tOut => AST.Typ.fn tIn tOut) out)
                = Outcome.yield (some typ) := by
            simpa [AST.Trm.infer] using hInfer
          simp [AST.Trm.eval]
          exact ⟨fuel + 1, by
            simp [AST.Val.infer, AST.Trm.infer, hFnInfer]
            change typ = typ
            rfl⟩
      | ref top =>
        simp [AST.Trm.eval]
        simp [AST.Trm.infer] at hInfer
        cases hInfer
        exact hEnv top
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
                      have hFnSafe := ih env hEnv fnTerm (.fn tIn typ) fuel hFn
                      have hArgSafe := ih env hEnv arg argTyp fuel hArg
                      cases hFnEval : fnTerm.eval env runtimeFuel with
                      | outOfFuel => simp [AST.Trm.eval, hFnEval]
                      | yield fnEvalResult =>
                        rw [hFnEval] at hFnSafe
                        cases fnEvalResult with
                        | none => cases hFnSafe
                        | some fnValue =>
                          rcases hFnSafe with ⟨fnFuel, hFnInfer⟩
                          cases fnValue with
                          | primitive repr =>
                            cases fnFuel with
                            | zero => simp [AST.Val.infer, AST.Trm.infer] at hFnInfer
                            | succ fnFuel =>
                              simp [AST.Val.infer, AST.Trm.infer] at hFnInfer
                              change AST.Typ.primitive = AST.Typ.fn tIn typ at hFnInfer
                              cases hFnInfer
                          | fn runtimeTIn body =>
                            cases fnFuel with
                            | zero => simp [AST.Val.infer, AST.Trm.infer] at hFnInfer
                            | succ bodyFuel =>
                              simp [AST.Val.infer, AST.Trm.infer] at hFnInfer
                              cases hBodyCompile : (body .ptop).infer bodyFuel with
                              | outOfFuel =>
                                rw [hBodyCompile] at hFnInfer
                                simp [Outcome.map] at hFnInfer
                              | yield bodyResult =>
                                cases bodyResult with
                                | none =>
                                  rw [hBodyCompile] at hFnInfer
                                  simp [Outcome.map] at hFnInfer
                                | some bodyTyp =>
                                  rw [hBodyCompile] at hFnInfer
                                  simp [Outcome.map] at hFnInfer
                                  change AST.Typ.fn runtimeTIn bodyTyp = AST.Typ.fn tIn typ at hFnInfer
                                  have hRuntimeTIn : runtimeTIn = tIn := (AST.Typ.fn.inj hFnInfer).1
                                  have hBodyTyp : bodyTyp = typ := (AST.Typ.fn.inj hFnInfer).2
                                  cases hRuntimeTIn
                                  cases hBodyTyp
                                  cases hArgEval : arg.eval env runtimeFuel with
                                  | outOfFuel => simp [AST.Trm.eval, hFnEval, hArgEval]
                                  | yield argEvalResult =>
                                    rw [hArgEval] at hArgSafe
                                    cases argEvalResult with
                                    | none => cases hArgSafe
                                    | some input =>
                                      rcases hArgSafe with ⟨inputFuel, hInputInfer⟩
                                      have hInputInferIn :
                                          input.CanInhabit tIn :=
                                        ⟨inputFuel, by
                                          have hArgEq : argTyp = tIn := hArgLe
                                          simpa [hArgEq] using hInputInfer⟩
                                      have hBodySafe :=
                                        ih (AST.Val.bindTop input)
                                          (by
                                            intro bodyTyp top
                                            cases top
                                            exact hInputInferIn)
                                          (body .ptop) typ bodyFuel hBodyCompile
                                      cases hBodyEval :
                                          (body .ptop).eval (AST.Val.bindTop input) runtimeFuel with
                                      | outOfFuel =>
                                        simp [AST.Trm.eval, hFnEval, hArgEval, hBodyEval]
                                      | yield bodyEvalResult =>
                                        rw [hBodyEval] at hBodySafe
                                        cases bodyEvalResult with
                                        | none => cases hBodySafe
                                        | some output =>
                                          simp [AST.Trm.eval, hFnEval, hArgEval, hBodyEval]
                                          exact hBodySafe
                    case neg =>
                      rw [hFn, hArg] at hInfer
                      simp [hArgLe] at hInfer

end InferAdequacy

end STLC_CE

end Lp2lc.Active
