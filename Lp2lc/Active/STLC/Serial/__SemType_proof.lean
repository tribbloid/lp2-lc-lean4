import «Lp2lc».Active.STLC.Serial.__SemType

namespace Lp2lc.Active.STLC.AST.Semantic

open Lp2lc.Active.Util

/-- Acceptance is preserved when the same search receives more fuel. -/
theorem checkMonotone {n} (trm : Trm n) (typ : Typ) (inputs : List Typ)
    (bindings : CheckBindings) {less more : Nat}
    (hFuel : less ≤ more) (hCheck : check trm typ inputs bindings less = true) :
    check trm typ inputs bindings more = true := by
  sorry

namespace Fundamental

private theorem applySafe {n} {fn arg : Trm n} {bindings : ExeBindings} {input output : Typ}
    (hFn : SemType fn bindings (.TFn input output)) (hArg : SemType arg bindings input) :
    SemType (.apply fn arg) bindings output := by
  sorry

private theorem checkSafe {n} {trm : Trm n} {typ : Typ} {inputs : List Typ}
    {source : CheckBindings} {target : ExeBindings} {fuel : Nat}
    (hCheck : check trm typ inputs source fuel = true) (hEnv : EnvFits source target) :
    SemType trm target typ := by
  sorry

/-- Accepted runtime terms cannot reject evaluation, and every result satisfies the semantic type. -/
theorem main {n} (trm : Trm n) (bindings : ExeBindings) (typ : Typ)
    (inputs : List Typ) (fuel : Nat)
    (hCheck : check trm typ inputs (bindings.map .inl) fuel = true) :
    SemType trm bindings typ := by
  sorry

end Fundamental

end Lp2lc.Active.STLC.AST.Semantic
