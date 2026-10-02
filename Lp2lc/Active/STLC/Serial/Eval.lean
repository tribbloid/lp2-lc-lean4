import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

/-- A source value together with the bindings captured when it was evaluated. -/
inductive RuntimeValue : Type 2 where
| mk {n refs} (value : AST n .val refs) (indices : refs → Nat) (captured : Nat → Option RuntimeValue)

namespace AST

/-- Evaluate with Nat-indexed bindings and a distinct index for each lexical slot.
Opening a function puts its argument at 0, leaves its unused context slot at 1, and shifts captures by 2.
-/
def eval {n refs} (self : AST n .trm refs) (indices : refs → Nat)
    (bindings : Nat → Option RuntimeValue) : RecOpt RuntimeValue := λ fuel =>
  match fuel, self with
  | 0, _ => .outOfFuel
  | _, .val value => .yield (some (.mk value indices bindings))
  | _, .ref carrier under => .yield (bindings (indices (under.shift (λ _ => .inl) carrier)))
  | fuel + 1, .apply fn arg =>
    match eval fn indices bindings fuel, eval arg indices bindings fuel with
    | .yield (some (.mk (.fn _ body) indices captured)), .yield (some value) =>
      eval (body.apply (.inr .only))
        (λ carrier => carrier.elim (λ prev => prev.elim (λ ref => indices ref + 2) (λ _ => 1)) (λ _ => 0))
        (λ index => match index with
          | 0 => some value
          | 1 => none
          | index + 2 => captured index) fuel
    | .yield _, .yield _ => .yield none
    | _, _ => .outOfFuel


/-- Evaluation that succeeds with smaller fuel succeeds with the same value at larger fuel. -/
theorem termEvalMonotone {n refs} (trm) (indices : refs → Nat) (bindings : Nat → Option RuntimeValue) :
    (eval (n := n) trm indices bindings).Monotone := by
  intro less more result hFuel hEval
  induction less using Nat.strongRecOn generalizing n refs trm indices bindings more result with
  | ind fromFuel ih =>
    cases fromFuel with
    | zero =>
      cases trm <;> simp [AST.eval] at hEval
    | succ fuel =>
      cases more with
      | zero => cases hFuel
      | succ toFuel =>
        have hFuelTail : fuel ≤ toFuel := Nat.le_of_succ_le_succ hFuel
        cases trm with
        | val value =>
          simpa [AST.eval] using hEval
        | apply fnTerm arg =>
          cases hFn : eval fnTerm indices bindings fuel with
          | outOfFuel => simp [AST.eval, hFn] at hEval
          | yield fnResult =>
            have hFnTop := ih fuel (Nat.lt_succ_self fuel)
              fnTerm indices bindings toFuel fnResult hFuelTail hFn
            cases hArg : eval arg indices bindings fuel with
            | outOfFuel => simp [AST.eval, hFn, hArg] at hEval
            | yield argResult =>
              have hArgTop := ih fuel (Nat.lt_succ_self fuel)
                arg indices bindings toFuel argResult hFuelTail hArg
              cases fnResult with
              | none =>
                simpa [AST.eval, hFn, hArg, hFnTop, hArgTop] using hEval
              | some fnValue =>
                cases fnValue with
                | mk value slots captured =>
                  cases value with
                  | lit repr =>
                    simpa [AST.eval, hFn, hArg, hFnTop, hArgTop] using hEval
                  | fn tIn body =>
                    cases argResult with
                    | none => simpa [AST.eval, hFn, hArg, hFnTop, hArgTop] using hEval
                    | some input =>
                      simp only [eval, hFn, hArg] at hEval
                      change eval (body.apply (.inr .only)) _ _ fuel = .yield result at hEval
                      have hBodyTop := ih fuel (Nat.lt_succ_self fuel)
                        _ _ _ toFuel result hFuelTail hEval
                      simpa [AST.eval, hFnTop, hArgTop] using hBodyTop
        | ref receipt under => simpa [AST.eval] using hEval

end AST

end Lp2lc.Active.STLC
