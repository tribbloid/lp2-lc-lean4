import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

local notation "𝒫" n:arg refs:arg => Parameters.withTRef (CtxEmbedding.toParameters (CtxEmbedding.DeBruijn n)) refs

/-- Runtime literals and closures with bindings indexed by lexical slot. -/
inductive RuntimeValue : Type 2 where
| lit (repr : String)
| private closure (n : Nat) (refs : URef) (level : Nat) (read : refs → Nat)
    (body : Pre.Binder (𝒫 n refs).Next .trm) (captured : Nat → Option RuntimeValue)

namespace AST

private def evalVisit {context refs} (trm : Pre.AST (𝒫 context refs) .trm)
    (level : Nat) (read : refs → Nat) (bindings : Nat → Option RuntimeValue) : RecOpt RuntimeValue := λ fuel =>
  match fuel, trm with
  | 0, _ => .outOfFuel
  | _, .val value =>
    .yield (some (match value with
      | .lit repr => .lit repr
      | .fn _ body => .closure context refs level read body bindings))
  | _, .ref carrier under => .yield (bindings (read (under.shift (λ _ => .inl) carrier)))
  | fuel + 1, .apply fn arg =>
    match evalVisit fn level read bindings fuel, evalVisit arg level read bindings fuel with
    | .yield (some (.closure _ _ scope read body captured)), .yield (some value) =>
      evalVisit (body.apply (.inr .only)) (scope + 2)
        (λ carrier => carrier.elim (λ prev => prev.elim read (λ _ => scope + 1)) (λ _ => scope + 2))
        (λ index => if index = scope + 2 then some value else if index = scope + 1 then none else captured index) fuel
    | .yield _, .yield _ => .yield none
    | _, _ => .outOfFuel

/-- Evaluate concrete De Bruijn syntax using the caller's known bindings. -/
def eval {n} (self : Trm n) (bindings : Nat → Option RuntimeValue) : RecOpt RuntimeValue :=
  evalVisit self n (λ _ => n) bindings

/-- Evaluation that succeeds with smaller fuel succeeds with the same value at larger fuel. -/
theorem termEvalMonotone {n} (trm : Trm n) (bindings : Nat → Option RuntimeValue) :
    (eval (n := n) trm bindings).Monotone := by
  have hVisit {context refs} (trm : Pre.AST (𝒫 context refs) .trm) (level : Nat)
      (read : refs → Nat) (bindings : Nat → Option RuntimeValue) :
      Rec.Monotone (evalVisit trm level read bindings) := by
    intro less more result hFuel hEval
    induction less using Nat.strongRecOn generalizing context refs trm level read bindings more result with
    | ind fromFuel ih =>
      cases fromFuel with
      | zero =>
        cases trm <;> simp [evalVisit] at hEval
      | succ fuel =>
        cases more with
        | zero => cases hFuel
        | succ toFuel =>
          have hFuelTail : fuel ≤ toFuel := Nat.le_of_succ_le_succ hFuel
          cases trm with
          | val value =>
            simpa [evalVisit] using hEval
          | apply fnTerm arg =>
            cases hFn : evalVisit fnTerm level read bindings fuel with
            | outOfFuel => simp [evalVisit, hFn] at hEval
            | yield fnResult =>
              have hFnTop := ih fuel (Nat.lt_succ_self fuel)
                fnTerm level read bindings toFuel fnResult hFuelTail hFn
              cases hArg : evalVisit arg level read bindings fuel with
              | outOfFuel => simp [evalVisit, hFn, hArg] at hEval
              | yield argResult =>
                have hArgTop := ih fuel (Nat.lt_succ_self fuel)
                  arg level read bindings toFuel argResult hFuelTail hArg
                cases fnResult with
                | none =>
                  simpa [evalVisit, hFn, hArg, hFnTop, hArgTop] using hEval
                | some fnValue =>
                  cases fnValue
                  next repr =>
                    simpa [evalVisit, hFn, hArg, hFnTop, hArgTop] using hEval
                  next context carriers scope read body captured =>
                    cases argResult with
                    | none => simpa [evalVisit, hFn, hArg, hFnTop, hArgTop] using hEval
                    | some input =>
                      have hBody : evalVisit (body.apply (.inr .only)) (scope + 2)
                          (λ carrier => carrier.elim
                            (λ prev => prev.elim read (λ _ => scope + 1)) (λ _ => scope + 2))
                          (λ index => if index = scope + 2 then some input
                            else if index = scope + 1 then none else captured index) fuel = .yield result := by
                        simpa [evalVisit, hFn, hArg] using hEval
                      have hBodyTop := ih fuel (Nat.lt_succ_self fuel)
                        _ _ _ _ toFuel result hFuelTail hBody
                      simpa [evalVisit, hFnTop, hArgTop] using hBodyTop
          | ref receipt under => simpa [evalVisit] using hEval
  exact hVisit trm n (λ _ => n) bindings

end AST

end Lp2lc.Active.STLC
