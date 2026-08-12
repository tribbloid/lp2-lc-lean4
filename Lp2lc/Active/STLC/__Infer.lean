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

namespace AST

/--
get the strongest post type bound (post-condition) of a term, or throw an error
-/
def infer [env: @BuildEnv F] (self : Trm F) : RecOpt (Typ F)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val (.lit _) => .yield (some .primitive)
    | .val (.lam body tIn) =>
      let index := env.trm2typCtx.getUId ⟨self, tIn⟩
      ((body index).infer fuel).map (λ out => out.map (λ tOut => .fn tIn tOut))
    | .apply fnTerm arg =>
      match fnTerm.infer fuel, arg.infer fuel with
      | .yield (some (.fn tIn tOut)), .yield (some argTyp) =>
        if argTyp ≤ tIn then .yield (some tOut) else .yield none
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none
    | @AST.ref _ i => .yield (some (env.trm2typCtx.inv i).typ)

/-- Inference that succeeds with smaller fuel succeeds with the same type at larger fuel. -/
theorem termInferMonotone [env : @BuildEnv F]
    (trm : Trm F) :
    trm.infer.Monotone := by
  intro less more result hFuel hInfer
  induction less using Nat.strongRecOn generalizing trm more result with
  | ind fromFuel ih =>
    cases fromFuel with
    | zero =>
      cases trm <;> simp [AST.infer] at hInfer
    | succ fuel =>
      cases more with
      | zero => cases hFuel
      | succ toFuel =>
        have hFuelTail : fuel <= toFuel := Nat.le_of_succ_le_succ hFuel
        cases trm with
        | val value =>
          cases value with
          | lit repr => simpa [AST.infer] using hInfer
          | lam body tIn =>
            cases hBody :
                (body (env.trm2typCtx.getUId ⟨.val (.lam body tIn), tIn⟩)).infer fuel with
            | outOfFuel => simp [AST.infer, hBody, Outcome.map] at hInfer
            | yield bodyResult =>
              have hBodyTop := ih fuel (Nat.lt_succ_self fuel)
                (body (env.trm2typCtx.getUId ⟨.val (.lam body tIn), tIn⟩))
                toFuel bodyResult hFuelTail hBody
              simpa [AST.infer, Outcome.map, hBody, hBodyTop] using hInfer
        | apply fnTerm arg =>
          cases hFn : fnTerm.infer fuel with
          | outOfFuel => simp [AST.infer, hFn] at hInfer
          | yield fnResult =>
            cases hArg : arg.infer fuel with
            | outOfFuel => simp [AST.infer, hFn, hArg] at hInfer
            | yield argResult =>
              have hFnTop := ih fuel (Nat.lt_succ_self fuel) fnTerm toFuel fnResult hFuelTail hFn
              have hArgTop := ih fuel (Nat.lt_succ_self fuel) arg toFuel argResult hFuelTail hArg
              simpa [AST.infer, hFn, hArg, hFnTop, hArgTop] using hInfer
        | ref id =>
          simpa [AST.infer] using hInfer

/-- Value inference monotonicity follows from term inference monotonicity. -/
theorem valueInferMonotone [env : @BuildEnv F]
    (value : AST.Val F) :
    (AST.val value).infer.Monotone :=
  termInferMonotone (AST.val value)


def CanInhabit (trm : Trm F) (typ : AST.Typ F) [@BuildEnv F] : Prop :=
  trm.infer.isDecidable (λ t2 => t2 <= typ)

end AST

class ProvingBase extends (@ExeEnv F), (@BuildEnv F)

/-
TODO: there is no need to use this complex definition, which is optimised for [CanInhabit] and requires both trm & typ to be provided

The simple conjecture is merely `∀ t : AST.Trm F, t.eval.infer <= t.infer`

There are few intricacies:

- `t` may already contain references to free variable in the context
  - `t.infer` should work even in this case
- the subtyping symbol `<=` is only applicable for AST with identical carrier, so `infer` is allowed to shift carrier, but `eval` is not

To avoid UId being abused to fake construction from any Fixpoint, the simple conjecture should be:

[]

The final objective is to produce a **conformal proof**, a proof that is structurally isomorphic to `Trm.infer` algorithm
-/

def Safety [@ProvingBase F] (trm : AST.Trm F) (typ : AST.Typ F) : Prop :=
  trm.eval.isSemiDecidable (λ v => (AST.val v).CanInhabit typ)

end

end STLC

end Lp2lc.Active
