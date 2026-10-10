import «Lp2lc».Active.STLC.UId.Eval

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util

/-- Compile-time minting accepts types or canonical values without requiring an executable environment. -/
class BuildEnv (refs : UIdRefs) where
  uid2bothCtx : KVEquiv refs.uid2both

namespace Root.Trm

/-- Infers terms from shared type or value receipts without executing values.

Binders substitute the receipt for their annotated input type into the canonical structural body.
-/
def infer {refs : UIdRefs} [env : BuildEnv refs] (self : refs.base.Trm) : RecOpt refs.base.Typ
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val (.lit _) => .yield (some .TLit)
    | .val (.fn tIn body) =>
      let receipt := env.uid2bothCtx.inv (.inl tIn)
      (infer (Root.Binder.apply body receipt) fuel).map (Option.map (.TFn tIn))
    | .apply fnTerm arg =>
      match infer fnTerm fuel, infer arg fuel with
      | .yield (some (.TFn tIn tOut)), .yield (some argTyp) =>
        .yield (if argTyp ≤ tIn then some tOut else none)
      | .yield _, .yield _ => .yield none
      | _, _ => .outOfFuel
    | .ref carrier under =>
      match refs.uid2both.get (mapRef under carrier) with
      | .inl typ => .yield (some typ)
      | .inr value => infer value.val.asTrm fuel

namespace Monotone

variable {refs : UIdRefs} [build : BuildEnv refs]

/-- Runtime inference preserves every completed result when fuel increases. -/
theorem termInfer (trm : refs.base.Trm) : trm.infer.Monotone := by
  exact inferVisit trm Sum.inr

end Monotone

end Root.Trm
end Lp2lc.Active.STLC
