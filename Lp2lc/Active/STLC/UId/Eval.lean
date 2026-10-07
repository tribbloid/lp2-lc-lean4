import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util

namespace AST

structure ExeEnv where
  UId : Type


/-- Evaluate using the caller's bindings. Every recursive resolution consumes one unit of fuel. -/
def eval {n} (self : Pre.Trm n) (bindings : ExeBindings := .empty) : RecOpt Pre.Val n := λ fuel =>
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
          (captured.set (context + 1) value) fuel
      | .yield _, .yield _ => .yield none
      | _, _ => .outOfFuel

end AST

end Lp2lc.Active.STLC
