import «Lp2lc».Active.STLC.UId.Eval

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util

/-- Compile-time minting accepts types or canonical values without requiring an executable environment. -/
class BuildEnv (refs : UIdRefs) where
  uid2bothCtx : KVEquiv refs.uid2both

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
      | .inr value, _ => visit value.val.asTrm Sum.inr fuel

namespace Monotone

variable {refs : UIdRefs} [build : BuildEnv refs]

theorem inferVisit {base : Root} (trm : base.Trm)
    (bindings : base.UId → refs.UId ⊕ refs.UId) (less more : Nat)
    (result : Option refs.base.Typ) (le : less ≤ more)
    (h : infer.visit trm bindings less = .yield result) :
    infer.visit trm bindings more = .yield result := by
  induction less generalizing base trm bindings more result with
  | zero => simp [infer.visit] at h
  | succ less ih =>
    cases more with
    | zero => omega
    | succ more =>
      have le := Nat.le_of_succ_le_succ le
      cases trm <;> try cases ‹Pre.AST _ .val›
      all_goals
        simp only [infer.visit.eq_2, infer.visit.eq_3, infer.visit.eq_4, infer.visit.eq_5,
          Rec.Outcome.map] at h ⊢
        repeat split at h
        all_goals simp_all

/-- Runtime inference preserves every completed result when fuel increases. -/
theorem termInfer (trm : refs.base.Trm) : trm.infer.Monotone := by
  exact inferVisit trm Sum.inr

end Monotone

end Root.Trm
end Lp2lc.Active.STLC
