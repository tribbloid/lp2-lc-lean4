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

namespace AST.Trm

/-- Value validity plus inference to a requested type bound. -/
def CanInhabit (self : AST.Trm ctx) (typ : AST.Typ) : Prop :=
  self.infer.isDecidable (λ inferred => inferred <= typ)

end AST.Trm


namespace AST.Val

/-- Infers a value by viewing it as a value term. -/
def infer {ctx : AST.Ctx} (self : AST.Val ctx) : RecOption AST.Typ :=
  AST.Trm.infer (AST.Trm.val self)

/-- Value validity plus inference to a requested type bound. -/
def CanInhabit {ctx : AST.Ctx} (self : AST.Val ctx) (typ : AST.Typ) : Prop :=
  self.infer.isDecidable (λ inferred => inferred <= typ)

end AST.Val

def Safety
    (trm : AST.Trm ctx) (typ : AST.Typ) : Prop :=
  (Trm.eval trm rt).isSemiDecidable (λ value => value.2.2.CanInhabit typ)

end STLC_CE

end Lp2lc.Active
