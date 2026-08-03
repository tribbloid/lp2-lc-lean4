import «Lp2lc».Active.STLC.STLCDef

namespace Tests.STLC_Eval.Sanity

open Lp2lc.Active.Util
open Lp2lc.Active.STLC

inductive Symbol

namespace Symbolic

abbrev I := Free.mkWeakest Symbol String

abbrev Typ := AST.Typ I
abbrev Val := AST.Val I
abbrev Trm := AST.Trm I

end Symbolic

open Symbolic

namespace Val

def vFalse : Val :=
  .lit "false"

def vTrue : Val :=
  .lit "true"

def idFn : Val :=
  .lam (λ ref => .ref ref) .primitive

end Val

end Sanity
