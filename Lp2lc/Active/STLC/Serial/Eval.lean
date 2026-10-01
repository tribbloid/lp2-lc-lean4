import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

/-- A source value together with the bindings captured when it was evaluated. -/
inductive RuntimeValue : Type 2 where
| mk (n : Nat) (refs : URef) (value : AST n .val refs) (captured : refs → Option RuntimeValue)

namespace AST

/-- Evaluate a term using the caller's known bindings. -/
def eval {n refs} (self : AST n .trm refs) (bindings : refs → Option RuntimeValue) : RecOpt RuntimeValue := λ fuel =>
  match fuel, self with
  | 0, _ => .outOfFuel
  | _, .val value => .yield (some (.mk n refs value bindings))
  | _, .ref carrier under => .yield (bindings (under.shift (λ _ => .inl) carrier))
  | fuel + 1, .apply fn arg =>
    match eval fn bindings fuel, eval arg bindings fuel with
    | .yield (some (.mk _ _ (.fn _ body) captured)), .yield (some value) =>
      eval (body.apply (.inr .only))
        (λ carrier => carrier.elim (λ prev => prev.elim captured (λ _ => none)) (λ _ => some value)) fuel
    | .yield _, .yield _ => .yield none
    | _, _ => .outOfFuel


/-- Evaluation that succeeds with smaller fuel succeeds with the same value at larger fuel. -/
theorem termEvalMonotone {n refs} (trm) (bindings : refs → Option RuntimeValue) :
    (eval (n := n) trm bindings).Monotone := by
  intro less more result hFuel hEval
  induction less using Nat.strongRecOn generalizing n refs trm bindings more result with
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
          cases hFn : eval fnTerm bindings fuel with
          | outOfFuel => simp [AST.eval, hFn] at hEval
          | yield fnResult =>
            have hFnTop := ih fuel (Nat.lt_succ_self fuel)
              fnTerm bindings toFuel fnResult hFuelTail hFn
            cases hArg : eval arg bindings fuel with
            | outOfFuel => simp [AST.eval, hFn, hArg] at hEval
            | yield argResult =>
              have hArgTop := ih fuel (Nat.lt_succ_self fuel)
                arg bindings toFuel argResult hFuelTail hArg
              cases fnResult with
              | none =>
                simpa [AST.eval, hFn, hArg, hFnTop, hArgTop] using hEval
              | some fnValue =>
                cases fnValue with
                | mk context carriers value captured =>
                  cases value with
                  | lit repr =>
                    simpa [AST.eval, hFn, hArg, hFnTop, hArgTop] using hEval
                  | fn tIn body =>
                    cases argResult with
                    | none => simpa [AST.eval, hFn, hArg, hFnTop, hArgTop] using hEval
                    | some input =>
                      have hBody : eval (body.apply (.inr .only))
                          (λ carrier => carrier.elim
                            (λ prev => prev.elim captured (λ _ => none)) (λ _ => some input))
                          fuel = .yield result := by
                        simpa [AST.eval, hFn, hArg] using hEval
                      have hBodyTop := ih fuel (Nat.lt_succ_self fuel)
                        _ _ toFuel result hFuelTail hBody
                      simpa [AST.eval, hFnTop, hArgTop] using hBodyTop
        | ref receipt under => simpa [AST.eval] using hEval

end AST

end Lp2lc.Active.STLC
