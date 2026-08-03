import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util
import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active

namespace STLC
open Lp2lc.Active.Util
open Lp2lc.Active.Util.Rec

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
      let index := env.trm2typCtx.getUID ⟨self, tIn⟩
      ((body index).infer fuel).map (λ out => out.map (λ tOut => .fn tIn tOut))
    | .apply fn arg =>
      match fn.infer fuel, arg.infer fuel with
      | .yield (some (.fn tIn tOut)), .yield (some argTyp) =>
        if argTyp ≤ tIn then .yield (some tOut) else .yield none
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none
    | @AST.Trm.ref _ i => .yield (some (env.trm2typCtx.inv i).typ)

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
            cases hBody :
                (body (env.trm2typCtx.getUID ⟨.val (.fn body tIn), tIn⟩)).infer fuel with
            | outOfFuel => simp [AST.Trm.infer, hBody, Outcome.map] at hInfer
            | yield bodyResult =>
              have hBodyTop := ih fuel (Nat.lt_succ_self fuel)
                (body (env.trm2typCtx.getUID ⟨.val (.fn body tIn), tIn⟩))
                toFuel bodyResult hFuelTail hBody
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


def CanInhabit (trm : Trm F) (typ : AST.Typ F) [@CompilerEnv F] : Prop :=
  trm.infer.isDecidable (λ t2 => t2 <= typ)

end AST.Trm

class ProvingBase extends (@RuntimeEnv F), (@CompilerEnv F)

def Safety [@ProvingBase F] (trm : AST.Trm F) (typ : AST.Typ F) : Prop :=
  trm.eval.isSemiDecidable (λ v => (AST.Trm.val v).CanInhabit typ)

end

end STLC

end Lp2lc.Active
