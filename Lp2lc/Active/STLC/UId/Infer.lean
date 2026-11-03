import «Lp2lc».Active.STLC.UId.Infra

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util

namespace Root.Trm

local instance {P} : LE (Pre.AST P .typ) := ⟨Eq⟩

@[instance_reducible]
local instance typDecidableLE {P} : DecidableLE (Pre.AST P .typ)
  | .TLit, .TLit => isTrue rfl
  | .TLit, .TFn _ _
  | .TFn _ _, .TLit => isFalse (λ equality => nomatch equality)
  | .TFn a b, .TFn c d =>
    @decidable_of_iff' _ _ (Pre.AST.TFn.injEq a b c d).to_iff
      (@instDecidableAnd _ _ (typDecidableLE a c) (typDecidableLE b d))

/-- Infers terms from shared type or value receipts without executing values.

Binders substitute the receipt for their annotated input type into the canonical structural body.
-/
def infer {refs : UIdRefs} [env : BuildEnv refs] (self : refs.base.Trm) : RecOpt refs.base.Typ
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .pure (.val (.lit _)) => .yield (some .TLit)
    | .pure (.val (.fn tIn body)) =>
      let receipt := env.uid2bothCtx.inv (.inl tIn)
      (infer (Root.Binder.apply body receipt) fuel).map (Option.map (.TFn tIn))
    | .apply fnTerm arg =>
      match infer fnTerm fuel, infer arg fuel with
      | .yield (some (.TFn tIn tOut)), .yield (some argTyp) =>
        .yield (if argTyp ≤ tIn then some tOut else none)
      | .yield _, .yield _ => .yield none
      | _, _ => .outOfFuel
    | .pure (.ref carrier under) =>
      match refs.uid2both.get (mapRef under carrier) with
      | .inl typ => .yield (some typ)
      | .inr value => infer value.asTrm fuel
    | .pure (.val (.fnPrimitive tOut _)) => .yield (some (.TFn .TLit tOut))

end Root.Trm
end Lp2lc.Active.STLC
