import «Lp2lc».Active.STLC.UId.__Infer

namespace Tests.STLC.UId
open Lp2lc.Active.STLC Lp2lc.Active.Util Root Root.Trm

section callbackOpening

-- Receipt-dependent unused branches cannot change the canonical evaluation or inference.
example {refs : UIdRefs} [BuildEnv refs] [ExeEnv refs] :
    let value : refs.base.Val := .fn .TLit (.mk (λ slot =>
      match slot with
      | .inl _ => .apply (.val (.lit "bad")) (.val (.lit "bad"))
      | .inr () => .val (.lit "canonical")))
    value.asTrm.infer 2 = .yield (some (.TFn .TLit .TLit)) ∧
      eval (refs := refs) (.apply value.asTrm (.val (.lit "argument"))) 2 =
        .yield (some (.lit "canonical")) :=
  ⟨rfl, rfl⟩

end callbackOpening

section sharedLookup

-- The same type receipt is accepted only in a lexical binding, never as a free runtime reference.
example {refs : UIdRefs} [BuildEnv refs] [ExeEnv refs] (receipt : refs.UId)
    (typ : refs.base.Typ) (lookup : refs.uid2both.get receipt = .inl typ) :
    infer (refs := refs) (.ref receipt .same) 1 = .yield none ∧
      eval (refs := refs) (.ref receipt .same) 1 = .yield none ∧
      Root.Trm.infer.visit (.ref receipt .same : refs.base.Trm)
        (λ _ => .inl receipt) 1 = .yield (some typ) := by
  simp [Root.Trm.infer, Root.Trm.infer.visit, Root.Trm.eval, Root.mapRef, lookup]

end sharedLookup

section runtimeSubstitution

-- Minting recovers normalized values; a nested ancestor reference still selects the first argument.
example {refs : UIdRefs} [exe : ExeEnv refs] (value : refs.base.Val) :
    let outer : refs.base.Val := .fn .TLit (.mk (λ _ =>
      .val (.fn .TLit (.mk (λ _ =>
        .ref (P' := refs.base.P.Next) (.inr ()) (.lower .same))))))
    eval (refs := refs)
      (.apply (.val (.fn .TLit (.mk (λ _ => .ref (P' := refs.base.P.Next) (.inr ()) .same))))
        value.asTrm) 2 =
      .yield (some (Root.canonicalVal value).val) ∧
      eval (refs := refs) (.apply (.apply outer.asTrm value.asTrm) (.val (.lit "newest"))) 3 =
        .yield (some (Root.canonicalVal value).val) := by
  let receipt := exe.uid2valCtx.inv (Root.canonicalVal value)
  have lookup : refs.uid2both.get receipt.val = .inr (Root.canonicalVal value) :=
    (Sum.inr_getRight _ _).symm.trans (congrArg Sum.inr (exe.uid2valCtx.rightInv _))
  constructor <;>
    change (match refs.uid2both.get receipt.val with
      | .inl _ => .yield none
      | .inr result => .yield (some result.val) : Rec.Outcome (Option refs.base.Val)) =
        .yield (some (Root.canonicalVal value).val)
  all_goals rw [lookup]

end runtimeSubstitution
end Tests.STLC.UId
