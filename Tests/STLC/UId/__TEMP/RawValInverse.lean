import «Lp2lc».Active.STLC.UId.Infra

namespace Tests.STLC.UId
open Lp2lc.Active.STLC Lp2lc.Active.Util

section rawValueInverse

-- The right inverse alone contradicts unrestricted function-valued binders.
example {base : Root} (refs : KVRefs base.UId base.Val) (ctx : KVEquiv refs) : False := by
  let inspect (value : base.Val) (receipt : base.UId) : Bool :=
    match value with
    | .lit _ => false
    | .fn _ (.mk body) =>
      match body (.inl receipt) with
      | .apply _ _ => true
      | _ => false
  let diagonal : base.Val := .fn .TLit (.mk (λ slot =>
    match slot with
    | .inl receipt =>
      if inspect (refs.get receipt) receipt then .val (.lit "")
      else .apply (.val (.lit "")) (.val (.lit ""))
    | .inr () => .val (.lit "")))
  let receipt := ctx.inv diagonal
  have opposite := congrArg (λ value => inspect value receipt) (ctx.rightInv diagonal)
  change inspect (refs.get receipt) receipt =
    (match (if inspect (refs.get receipt) receipt then
        (.val (.lit "") : base.AST .trm (base.UId ⊕ Unit))
      else .apply (.val (.lit "")) (.val (.lit ""))) with
    | .apply _ _ => true
    | _ => false) at opposite
  cases bit : inspect (refs.get receipt) receipt <;>
    simp [bit] at opposite

end rawValueInverse

section canonicalValueImage

-- Normalization discards the unused callback inputs, including the diagonal branch.
example {base : Root} (choose : base.UId → base.AST .trm (base.UId ⊕ Unit)) :
    Root.AST.recarrier (.fn .TLit (.mk (λ slot =>
      match slot with
      | .inl receipt => choose receipt
      | .inr () => .val (.lit ""))) : base.Val) id =
      .fn .TLit (.mk (λ _ => .val (.lit ""))) := rfl

-- Membership in the image records the observed value rather than the original callback.
example {base : Root} (value : base.Val) :
    ∃ source : base.Val, Root.AST.recarrier source id = Root.AST.recarrier value id :=
  ⟨value, rfl⟩

end canonicalValueImage
end Tests.STLC.UId
