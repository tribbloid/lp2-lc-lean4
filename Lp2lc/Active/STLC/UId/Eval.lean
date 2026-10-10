import «Lp2lc».Active.STLC.UId.Infra

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util

namespace Root.Val

/-- Value identity observes only canonical binder bodies, including beneath nested binders. -/
def Same {base : Root} (left right : base.Val) : Prop :=
  AST.recarrier left id = AST.recarrier right id

end Root.Val

/-- Runtime minting is limited to values; receipt identity ignores unused callback inputs.

A raw `KVEquiv` on functional values would require equality at every callback input, contradicting
UId's canonical-opening contract. The equivalence therefore stores canonical-value observations.
-/
class ExeEnv (refs : UIdRefs) where
  uid2val : refs.uid2both.Lesser refs.UId refs.base.Val
  uid2valCtx : KVEquiv (⟨λ receipt => Quot.mk _ (uid2val.get receipt)⟩ :
    KVRefs refs.UId (Quot (Root.Val.Same (base := refs.base))))
  valueOnly : uid2val.upcastV.toFun = Sum.inr

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
        let receipt := exe.uid2val.upcastK (exe.uid2valCtx.inv (Quot.mk _ arg))
        eval (Root.Binder.apply body receipt) fuel
      | .yield _, .yield _ => .yield none
      | _, _ => .outOfFuel
    | .ref carrier under =>
      match refs.uid2both.get (mapRef under carrier) with
      | .inl _ => .yield none
      | .inr value => .yield (some value)

end Root.Trm
end Lp2lc.Active.STLC
