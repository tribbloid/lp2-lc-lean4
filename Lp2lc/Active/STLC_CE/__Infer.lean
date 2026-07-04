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
    | .val (.fn _ tIn body) =>
      (infer (body .ptop) fuel).map (fun out => out.map (fun tOut => .fn tIn tOut))
    | .apply fn arg =>
      match infer fn fuel, infer arg fuel with
      | .yield (some (.fn tIn tOut)), .yield (some argTyp) =>
        if argTyp ≤ tIn then .yield (some tOut) else .yield none
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none
    | @AST.Trm.ref _ _ typ _ _ => .yield (some typ)

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
          | fn _ tIn body =>
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
        | ref inst top =>
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

end AST.Val

mutual

/-- Values whose captured CE environments and function bodies are valid. -/
inductive AST.Val.Valid : AST.Val -> Prop where
| primitive {repr : AST.Data} : AST.Val.Valid (.primitive repr)
| fn {ctx : AST.Ctx} {env : AST.RuntimeEnv ctx} {tIn : AST.Typ}
    {body : AST.ProxyTop (ctx :/: tIn) tIn -> AST.Trm (ctx :/: tIn)} :
    AST.RuntimeEnv.Valid env ->
    ((top : AST.ProxyTop (ctx :/: tIn) tIn) -> AST.Trm.Valid (body top)) ->
    AST.Val.Valid (.fn env tIn body)

/-- Runtime environments whose entries are valid and infer to their context type. -/
inductive AST.RuntimeEnv.Valid : {ctx : AST.Ctx} -> AST.RuntimeEnv ctx -> Prop where
| empty : AST.RuntimeEnv.Valid .empty
| snoc {ctx : AST.Ctx} {typ : AST.Typ} {env : AST.RuntimeEnv ctx}
    {value : AST.Val} :
    AST.RuntimeEnv.Valid env ->
    AST.Val.Valid value ->
    value.infer.isDecidable (fun inferred => inferred <= typ) ->
    AST.RuntimeEnv.Valid (.snoc (typ := typ) env value)

/-- Terms whose embedded values carry valid captured environments. -/
inductive AST.Trm.Valid : {ctx : AST.Ctx} -> AST.Trm ctx -> Prop where
| val {ctx : AST.Ctx} {value : AST.Val} :
    AST.Val.Valid value -> AST.Trm.Valid (ctx := ctx) (.val value)
| apply {ctx : AST.Ctx} {fn arg : AST.Trm ctx} :
    AST.Trm.Valid fn -> AST.Trm.Valid arg -> AST.Trm.Valid (.apply fn arg)
| ref {ctx varCtx : AST.Ctx} {typ : AST.Typ}
    {inst : AST.ReifyIndex varCtx ctx typ} {top : AST.ProxyTop varCtx typ} :
    AST.Trm.Valid (.ref inst top)

end

namespace AST.Val

/-- Value validity plus inference to a requested type bound. -/
def SafeAs (self : AST.Val) (typ : AST.Typ) : Prop :=
  self.Valid ∧ self.infer.isDecidable (fun inferred => inferred <= typ)

end AST.Val

namespace AST.RuntimeEnv

/-- Loading from a valid CE environment produces a value safe for the variable type. -/
theorem loadSafety {targetCtx varCtx : AST.Ctx} {typ : AST.Typ}
    {env : AST.RuntimeEnv targetCtx}
    (hEnv : AST.RuntimeEnv.Valid env)
    (inst : AST.ReifyIndex varCtx targetCtx typ)
    (top : AST.ProxyTop varCtx typ) :
    (env.load inst top).SafeAs typ := by
  induction inst with
  | refl =>
    cases top
    cases env with
    | snoc env value =>
      cases hEnv with
      | snoc hTail hValue hInfer =>
        exact ⟨hValue, hInfer⟩
  | snoc inst ih =>
    cases env with
    | snoc env value =>
      cases hEnv with
      | snoc hTail hValue hInfer =>
        exact ih hTail top

end AST.RuntimeEnv

def Safety : Prop :=
  ∀ {ctx : AST.Ctx} (env : AST.RuntimeEnv ctx),
  AST.RuntimeEnv.Valid env ->
  ∀ (trm : AST.Trm ctx),
    AST.Trm.Valid trm ->
  ∀ (typ : AST.Typ) (fuel : Nat),
    trm.infer fuel = Outcome.yield (.some typ) ->
    (trm.eval env).isSemiDecidable (fun value => value.SafeAs typ)

namespace Safety

def proof : Safety := by
  intro ctx env hEnv trm hTrm typ fuel hInfer runtimeFuel
  induction runtimeFuel generalizing ctx env hEnv trm hTrm typ fuel with
  | zero => rfl
  | succ runtimeFuel ih =>
    cases fuel with
    | zero =>
      cases trm <;> simp [AST.Trm.infer] at hInfer
    | succ fuel =>
      cases trm with
      | val value =>
        cases hTrm with
        | val hValue =>
          cases value with
          | primitive repr =>
            have hPrim : AST.Typ.primitive = typ := by
              simpa [AST.Trm.infer] using hInfer
            simp [AST.Trm.eval]
            exact ⟨hValue,
              ⟨fuel + 1, by
                simp [AST.Val.infer, AST.Trm.infer]
                change AST.Typ.primitive = typ
                exact hPrim⟩⟩
          | fn closureEnv tIn body =>
            have hFnInfer :
                ((body AST.ProxyTop.ptop).infer fuel).map
                  (fun out => Option.map (fun tOut => AST.Typ.fn tIn tOut) out)
                  = Outcome.yield (some typ) := by
              simpa [AST.Trm.infer] using hInfer
            simp [AST.Trm.eval]
            exact ⟨hValue,
              ⟨fuel + 1, by
                simp [AST.Val.infer, AST.Trm.infer, hFnInfer]
                change typ = typ
                rfl⟩⟩
      | ref inst top =>
        cases hTrm
        simp [AST.Trm.eval]
        simp [AST.Trm.infer] at hInfer
        cases hInfer
        exact AST.RuntimeEnv.loadSafety hEnv inst top
      | apply fnTerm arg =>
        cases hTrm with
        | apply hFnTrm hArgTrm =>
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
                      have hFnSafe := ih env hEnv fnTerm hFnTrm (.fn tIn typ) fuel hFn
                      have hArgSafe := ih env hEnv arg hArgTrm argTyp fuel hArg
                      cases hFnEval : fnTerm.eval env runtimeFuel with
                      | outOfFuel => simp [AST.Trm.eval, hFnEval]
                      | yield fnEvalResult =>
                        rw [hFnEval] at hFnSafe
                        cases fnEvalResult with
                        | none => cases hFnSafe
                        | some fnValue =>
                          rcases hFnSafe with ⟨hFnValid, hFnInfer⟩
                          cases fnValue with
                          | primitive repr =>
                            rcases hFnInfer with ⟨fnFuel, hFnInfer⟩
                            cases fnFuel with
                            | zero => simp [AST.Val.infer, AST.Trm.infer] at hFnInfer
                            | succ fnFuel =>
                              simp [AST.Val.infer, AST.Trm.infer] at hFnInfer
                              change AST.Typ.primitive = AST.Typ.fn tIn typ at hFnInfer
                              cases hFnInfer
                          | fn closureEnv runtimeTIn body =>
                            rcases hFnInfer with ⟨fnFuel, hFnInfer⟩
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
                                  cases hFnValid with
                                  | fn hClosureEnv hBodyTrm =>
                                    cases hArgEval : arg.eval env runtimeFuel with
                                    | outOfFuel => simp [AST.Trm.eval, hFnEval, hArgEval]
                                    | yield argEvalResult =>
                                      rw [hArgEval] at hArgSafe
                                      cases argEvalResult with
                                      | none => cases hArgSafe
                                      | some input =>
                                        rcases hArgSafe with ⟨hInputValid, hInputInfer⟩
                                        have hInputInferIn :
                                            input.infer.isDecidable (fun inferred => inferred <= tIn) := by
                                          rcases hInputInfer with ⟨inputFuel, hInputInfer⟩
                                          have hArgEq : argTyp = tIn := hArgLe
                                          exact ⟨inputFuel, by
                                            simpa [hArgEq] using hInputInfer⟩
                                        have hBodySafe :=
                                          ih (.snoc closureEnv input)
                                            (AST.RuntimeEnv.Valid.snoc hClosureEnv hInputValid hInputInferIn)
                                            (body .ptop) (hBodyTrm .ptop) typ bodyFuel hBodyCompile
                                        cases hBodyEval :
                                            (body .ptop).eval (.snoc closureEnv input) runtimeFuel with
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

end Safety

end STLC_CE

end Lp2lc.Active
