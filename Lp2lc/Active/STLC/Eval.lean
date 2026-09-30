import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

/-- A source value together with the bindings captured when it was evaluated. -/
inductive RuntimeValue : Type 2 where
| mk (n : Nat) (refs : URef) (value : AST .val n refs)
    (captured : refs → Option RuntimeValue) : RuntimeValue

/-- Evaluate a term using the caller's known bindings. -/
def AST.eval {n refs} (self : AST .trm n refs)
    (bindings : refs → Option RuntimeValue) : RecOpt RuntimeValue := λ fuel =>
  match fuel, self with
  | 0, _ => .outOfFuel
  | _, .val value => .yield (some (.mk n refs value bindings))
  | _, .ref carrier => .yield (bindings carrier)
  | fuel + 1, .apply fn arg =>
    match eval fn bindings fuel, eval arg bindings fuel with
    | .yield (some (.mk _ _ (.fn _ body) captured)), .yield (some value) =>
      eval (body.apply (.inr .only)) (λ carrier => carrier.elim captured (λ _ => some value)) fuel
    | .yield _, .yield _ => .yield none
    | _, _ => .outOfFuel

end Lp2lc.Active.STLC
