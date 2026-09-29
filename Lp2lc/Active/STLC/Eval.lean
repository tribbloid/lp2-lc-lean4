import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

/-- A source value together with the bindings captured when it was evaluated. -/
inductive RuntimeValue : Type 2 where
| mk (context : Nat) (value : AST.Val (AST.At context))
    (captured : (AST.At context).TRef → Option RuntimeValue) : RuntimeValue

abbrev Bindings (c : Nat) := (AST.At c).TRef → Option RuntimeValue

namespace AST.Trm

/-- Evaluate a term using the caller's known bindings. -/
def eval (self : AST.Trm (AST.At c)) (bindings : Bindings c) : RecOpt RuntimeValue
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | Pre.AST.val value => .yield (some (.mk c value bindings))
    | Pre.AST.ref carrier => .yield (bindings carrier)
    | Pre.AST.apply fn arg =>
      match eval fn bindings fuel, eval arg bindings fuel with
      | Rec.Outcome.yield (some (RuntimeValue.mk source (Pre.AST.fn _ body) captured)),
          Rec.Outcome.yield (some value) =>
        eval (c := source + 1) (body.apply (.inr .only))
          (λ carrier =>
            match carrier with
            | .inl prior => captured prior
            | .inr _ => some value) fuel
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none

end AST.Trm

end Lp2lc.Active.STLC
