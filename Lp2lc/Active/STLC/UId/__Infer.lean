import «Lp2lc».Active.STLC.UId.Eval

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util

/-- Compile-time minting accepts types or canonical values without requiring an executable environment. -/
class BuildEnv (refs : UIdRefs) where
  uid2bothCtx : KVEquiv (⟨λ receipt => Sum.map id (Quot.mk _) (refs.uid2both.get receipt)⟩ :
    KVRefs refs.UId (refs.base.Typ ⊕ Quot (Root.Val.Same (base := refs.base))))

namespace Root.Trm

/-- Infers runtime terms without executing values; lexical build bindings may contain values or types.

Bindings retain their origin: left receipts belong to lexical build slots, while right receipts are
runtime references. Binders open only at `.inr ()` and bind that slot to the minted type receipt without
merging it with free references. Stored values are inferred with runtime references only.
-/
def infer {refs : UIdRefs} [env : BuildEnv refs] (self : refs.base.Trm) : RecOpt refs.base.Typ :=
  visit self Sum.inr
where
  visit {base : Root} (self : base.Trm) (bindings : base.UId → refs.UId ⊕ refs.UId) : RecOpt refs.base.Typ
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val (.lit _) => .yield (some .TLit)
    | .val (.fn tIn body) =>
      let input := AST.recarrier tIn (Sum.elim id id ∘ bindings)
      let receipt := env.uid2bothCtx.inv (.inl input)
      (visit (base := ⟨base.UId ⊕ Unit⟩) (Pre.Binder.apply body (.inr ()))
        (Sum.elim bindings (λ _ => .inl receipt)) fuel).map (Option.map (.TFn input))
    | .apply fnTerm arg =>
      match visit fnTerm bindings fuel, visit arg bindings fuel with
      | .yield (some (.TFn tIn tOut)), .yield (some argTyp) =>
        .yield (if argTyp ≤ tIn then some tOut else none)
      | .yield _, .yield _ => .yield none
      | _, _ => .outOfFuel
    | .ref carrier under =>
      let origin := bindings (mapRef under carrier)
      match refs.uid2both.get (origin.elim id id), origin with
      | .inl typ, .inl _ => .yield (some typ)
      | .inl _, .inr _ => .yield none
      | .inr value, _ => visit value.asTrm Sum.inr fuel

end Root.Trm
end Lp2lc.Active.STLC
