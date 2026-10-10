import «Lp2lc».Active.STLC.UId.Infra

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util

namespace Root.Trm

/-- Evaluates through shared value receipts and structurally substitutes the minted argument.

Type-only receipts are rejected. Every recursive call consumes predecessor fuel; the callback
receives only `.inr ()`, never the runtime receipt being substituted into its canonical body.
-/
def eval {refs : UIdRefs} [build : BuildEnv refs] (self : refs.base.Trm) : RecOpt refs.base.Val
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield (some value)
    | .apply fnTerm arg =>
      match eval fnTerm fuel, eval arg fuel with
      | .yield (some (.fn _ body)), .yield (some arg) =>
        eval (Root.Binder.apply body (build.uid2val arg)) fuel
      | .yield _, .yield _ => .yield none
      | _, _ => .outOfFuel
    | .ref carrier under =>
      match refs.uid2both.get (mapRef under carrier) with
      | .inl _ => .yield none
      | .inr value => .yield (some value)

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

end Monotone

end Root.Trm
end Lp2lc.Active.STLC
