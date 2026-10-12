import «Lp2lc».Active.STLC.Serial.__SemType

namespace Lp2lc.Active.STLC.AST.Semantic

open Lp2lc.Active.Util

namespace Monotone

/-- Typing evidence remains valid when the fuel bound increases. -/
theorem termCheck {n} (trm : Trm n) (bindings : CompilerBindings)
    {less more : Nat} {typ : Typ} (hFuel : less ≤ more)
    (hType : semType trm bindings less typ) : semType trm bindings more typ := by
  sorry

end Monotone

namespace Fundamental

variable {n} (trm : Trm n) (bindings : ExeBindings)

/-- Evaluation cannot reject, and every returned closure has the requested type. -/
def safety (typ : Typ) : Prop :=
  (trm.eval bindings).isSemiDecidable (λ result =>
    ∃ fuel, semType result.value.asTrm (result.captured.map .inl) fuel typ)

/-- Semantic typing excludes evaluation rejection and preserves the result's type. -/
theorem main (fuel : Nat) (typ : Typ)
    (hType : semType trm (bindings.map .inl) fuel typ) : safety trm bindings typ := by
  sorry

end Fundamental

end Lp2lc.Active.STLC.AST.Semantic
