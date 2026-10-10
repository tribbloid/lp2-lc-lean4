import «Lp2lc».Active.STLC.UId.Infra

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util

/-- Runtime receipts identify values by their canonical structural syntax.

`Root.Binder.apply` already supplies uniform receipt substitution through its fixed `.inr ()` body.
This context represents those canonical observations with ordinary Lean equality on structural values.
-/
class ExeEnv (refs : UIdRefs) where
  uid2valCtx : KVEquiv refs.uid2val

namespace Root.Trm

/-- Evaluates through shared value receipts and structurally substitutes the minted argument.

Type-only receipts are rejected. Every recursive call consumes predecessor fuel; the callback
receives only `.inr ()`, never the runtime receipt being substituted into its canonical body.
-/
def eval {refs : UIdRefs} [exe : ExeEnv refs] (self : refs.base.Trm) : RecOpt refs.base.Val
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield (some value)
    | .apply fnTerm arg =>
      match eval fnTerm fuel, eval arg fuel with
      | .yield (some (.fn _ body)), .yield (some arg) =>
        eval (Root.Binder.apply body (exe.uid2valCtx.inv (Root.canonicalVal arg))) fuel
      | .yield _, .yield _ => .yield none
      | _, _ => .outOfFuel
    | .ref carrier under =>
      match refs.uid2both.get (mapRef under carrier) with
      | .inl _ => .yield none
      | .inr value => .yield (some value.val)

end Root.Trm
end Lp2lc.Active.STLC
