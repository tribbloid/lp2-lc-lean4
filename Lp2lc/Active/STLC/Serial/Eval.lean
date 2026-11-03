import «Lp2lc».Active.STLC.Serial.Infer

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util

namespace AST

/-- Evaluate using the caller's bindings, preserving rejection separately from runtime corruption.
Every recursive resolution consumes one unit of fuel. -/
def eval {n} (self : Trm n) (bindings : ExeBindings := .empty) : RecOpt (Return ExeVal) := λ fuel =>
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    letI : DecidableEq (Option Typ) := Option.instDecidableEq (inst := typDecidableLE)
    match self with
    | .pure (.val value) => .yield (some (.some (.mk n value bindings)))
    | .pure (.ref _ under) => .yield ((bindings under.sourceIndex.down).map .some)
    | .apply fn arg =>
      match eval fn bindings fuel, eval arg bindings fuel with
      | .yield (some (.some (.mk context (.fn tIn body) captured))), .yield (some (.some value)) =>
        (infer value.value.asTrm value.captured fuel).flatMap (λ result =>
          if result = some (resolveType tIn) then
            eval (body.apply .only) (captured.set (context + 1) value) fuel
          else .yield none)
      | .yield (some (.some (.mk context (.fnPrimitive tOut op) captured))),
          .yield (some (.some (.mk _ (.lit repr) _))) =>
        let value := op repr
        (infer (.pure (.val value)) captured fuel).map (λ result =>
          some (if result = some (resolveType tOut) then .some ⟨context, value, captured⟩ else .corrupted))
      | .yield (some .corrupted), .yield (some _)
      | .yield (some _), .yield (some .corrupted) => .yield (some .corrupted)
      | .yield _, .yield _ => .yield none
      | _, _ => .outOfFuel

end AST

end Lp2lc.Active.STLC
