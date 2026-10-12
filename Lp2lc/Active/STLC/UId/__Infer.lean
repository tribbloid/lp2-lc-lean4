import «Lp2lc».Active.STLC.UId.Eval
import «Lp2lc».Active.STLC.Serial.__Infer

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util

namespace Root.Trm

local instance {P} : DecidableEq (Pre.AST P .typ) := AST.typDecidableLE

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
        .yield (if argTyp = tIn then some tOut else none)
      | .yield _, .yield _ => .yield none
      | _, _ => .outOfFuel
    | .ref carrier under =>
      match refs.uid2both.get (mapRef under carrier) with
      | .inl typ => .yield (some typ)
      | .inr value => infer value.asTrm fuel

namespace Monotone

variable {refs : UIdRefs} [build : BuildEnv refs]

/-- Runtime inference preserves every completed result when fuel increases. -/
theorem termInfer (trm : refs.base.Trm) : trm.infer.Monotone := by
  intro less more result le h
  induction less generalizing trm more result with
  | zero => simp [infer] at h
  | succ less ih =>
    cases more <;> try omega
    have le := Nat.le_of_succ_le_succ le
    cases trm <;> try cases ‹Pre.AST _ .val›
    all_goals
      simp only [infer.eq_2, infer.eq_3, infer.eq_4, infer.eq_5, Rec.Outcome.map] at h ⊢
      repeat split at h
      all_goals simp_all
      all_goals exact λ impossible => (impossible rfl).elim

end Monotone

end Root.Trm
end Lp2lc.Active.STLC
