import «Lp2lc».Active.STLC.UId.Eval

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util

/-- Compile-time minting is limited to the type view of the shared receipt table. -/
class BuildEnv (refs : UIdRefs) where
  uid2typ : refs.uid2any.Lesser refs.UId refs.base.Typ
  uid2typCtx : KVEquiv uid2typ.toKVRefs
  typeOnly : uid2typ.upcastV.toFun = Sum.inr

namespace EnvBase.Trm

/-- Infers from shared values or types without executing values or minting value receipts.

Binders open only at `.inr ()`; the minted type receipt replaces that structural slot.
Every recursive inference consumes predecessor fuel, including a shared value lookup.
-/
def infer {refs : UIdRefs} [env : BuildEnv refs] (self : refs.base.Trm) : RecOpt refs.base.Typ
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val (.lit _) => .yield (some .TLit)
    | .val (.fn tIn body) =>
      let receipt := env.uid2typ.upcastK (env.uid2typCtx.inv tIn)
      (infer (EnvBase.Binder.apply body receipt) fuel).map (Option.map (.TFn tIn))
    | .apply fnTerm arg =>
      match infer fnTerm fuel, infer arg fuel with
      | .yield (some (.TFn tIn tOut)), .yield (some argTyp) =>
        .yield (if argTyp ≤ tIn then some tOut else none)
      | .yield _, .yield _ => .yield none
      | _, _ => .outOfFuel
    | .ref carrier under =>
      match refs.uid2any.get (mapRef under (.mk id) carrier) with
      | .inl value => infer value.asTrm fuel
      | .inr typ => .yield (some typ)

end EnvBase.Trm
end Lp2lc.Active.STLC
