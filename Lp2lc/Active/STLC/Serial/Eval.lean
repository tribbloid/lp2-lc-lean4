import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

/-- A source value together with the bindings captured when it was evaluated. -/
structure RuntimeValue : UAST where
  n : Nat
  value : Val n
  captured : Nat -> Option RuntimeValue

abbrev Captured := Nat → Option RuntimeValue -- append-only

namespace AST

/-- Evaluate using the caller's bindings. Every recursive resolution consumes one unit of fuel. -/
def eval {n} (self : Trm n) (bindings : Nat → Option RuntimeValue) : RecOpt RuntimeValue := λ fuel =>
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield (some (.mk n value bindings))
    | .ref _ under => .yield (bindings under.sourceIndex)
    | .apply fn arg =>
      match eval fn bindings fuel, eval arg bindings fuel with
      | .yield (some (.mk context (.fn _ body) captured)), .yield (some value) =>
        eval (body.apply .only)
          (λ index => if index = context + 2 then some value
            else if index = context + 1 then none else captured index) fuel
      | .yield _, .yield _ => .yield none
      | _, _ => .outOfFuel

/-- Evaluation that succeeds with smaller fuel succeeds with the same value at larger fuel. -/
theorem termEvalMonotone {n} (trm) (bindings : Nat → Option RuntimeValue) :
    (eval (n := n) trm bindings).Monotone := by
  intro less more result hFuel hEval
  induction less generalizing n trm bindings more result with
  | zero => simp [eval] at hEval
  | succ fuel ih =>
    cases more with
    | zero => cases hFuel
    | succ more =>
      have hFuelTail := Nat.le_of_succ_le_succ hFuel
      cases trm <;> simp only [eval.eq_2, eval.eq_3, eval.eq_4] at hEval ⊢
      all_goals
        repeat split at hEval
        all_goals simp_all

end AST

end Lp2lc.Active.STLC
