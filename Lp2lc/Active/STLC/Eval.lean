import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

/-- A source value together with the bindings captured when it was evaluated. -/
inductive RuntimeValue : Type 2 where
| mk (context : Nat) (value : AST.Val (AST.At context))
    (captured : Nat → Option RuntimeValue) : RuntimeValue

abbrev Bindings := Nat → Option RuntimeValue

namespace AST.Trm

/-- Evaluate a term using the caller's known bindings. -/
def eval (self : AST.Trm (AST.At c)) (bindings : Bindings) : RecOpt RuntimeValue
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield (some (.mk c value bindings))
    | .ref (source := source) _ _ => .yield (bindings source)
    | .apply fn arg =>
      match fn.eval bindings fuel, arg.eval bindings fuel with
      | .yield (some (.mk source (.fn _ body) captured)), .yield (some value) =>
        eval (body.apply .only) (λ slot => if slot = source then some value else captured slot) fuel
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none

end AST.Trm

end Lp2lc.Active.STLC
