import «Lp2lc».Active.STLC.UId.Infra

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util

namespace Root.Trm

/-- Evaluates through shared value receipts and structurally substitutes the minted argument.

Type-only receipts are rejected. Every recursive call consumes predecessor fuel; the callback
receives only `.inr ()`, never the runtime receipt being substituted into its canonical body.
-/
def eval {refs : UIdRefs} [build : BuildEnv refs] (self : refs.base.Trm) : RecOpt (Return refs.base.Val)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield (some (.some value))
    | .apply fnTerm arg =>
      match eval fnTerm fuel, eval arg fuel with
      | .yield (some (.some (.fn _ body))), .yield (some (.some arg)) =>
        eval (Root.Binder.apply body (build.uid2val arg)) fuel
      | .yield (some .corrupted), .yield (some _)
      | .yield (some _), .yield (some .corrupted) => .yield (some .corrupted)
      | .yield _, .yield _ => .yield none
      | _, _ => .outOfFuel
    | .ref carrier under => .yield ((refs.uid2both.get (mapRef under carrier)).getRight?.map .some)

namespace Monotone

/-- Evaluation preserves every completed result, including rejection, when fuel increases. -/
theorem termEval {refs : UIdRefs} [build : BuildEnv refs] (trm : refs.base.Trm) :
    trm.eval.Monotone := by
  intro less more result hFuel hEval
  induction less generalizing trm more result with
  | zero => simp [eval] at hEval
  | succ fuel ih =>
    cases more <;> try omega
    replace hFuel := Nat.le_of_succ_le_succ hFuel
    cases trm <;> simp only [eval.eq_2, eval.eq_3, eval.eq_4] at hEval ⊢
    all_goals
      repeat split at hEval
      all_goals simp_all
      all_goals subst_vars; cases ‹Return refs.base.Val› <;> (try cases ‹refs.base.Val›) <;> rfl

end Monotone

end Root.Trm
end Lp2lc.Active.STLC
