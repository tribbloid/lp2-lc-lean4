import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.Util.Parameters

/-- Supplies a fresh binder receipt and extends its captured bindings. -/
class RefBinding (TRefInc : URef → URef) where
  fresh (refs : URef) : TRefInc refs
  bind {V : Type 2} {refs : URef} (captured : refs → Option V) (value : V)
      (carrier : TRefInc refs) : Option V

instance {slot : URef} [Inhabited slot] : RefBinding (λ refs => refs ⊕ slot) where
  fresh _ := .inr default
  bind captured value carrier := carrier.elim captured (λ _ => some value)

end Lp2lc.Active.Util.Parameters

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

/-- A source value together with the bindings captured when it was evaluated. -/
inductive RuntimeValue (B : UByteCode) (TRefInc : URef → URef) : Type 2 where
| mk (refs : URef) (value : AST.Val { B, TRef := refs, TRefInc })
    (captured : refs → Option (RuntimeValue B TRefInc)) : RuntimeValue B TRefInc

namespace AST.Trm

/-- Evaluate a term using the caller's known bindings. -/
def eval {P : Parameters} [binding : Parameters.RefBinding P.TRefInc] (self : AST.Trm P)
    (bindings : P.TRef → Option (RuntimeValue P.B P.TRefInc)) : RecOpt (RuntimeValue P.B P.TRefInc)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield (some (.mk P.TRef value bindings))
    | .ref carrier => .yield (bindings carrier)
    | .apply fnTerm arg =>
      match eval fnTerm bindings fuel, eval arg bindings fuel with
      | Rec.Outcome.yield (some (RuntimeValue.mk source (.fn _ body) captured)),
          Rec.Outcome.yield (some value) =>
        eval (P := P.withTRef (P.TRefInc source))
          (body.apply (binding.fresh source)) (binding.bind captured value) fuel
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none

end AST.Trm

end Lp2lc.Active.STLC
