import «Lp2lc».Active.STLC.STLCDef

namespace Tests.STLC.Sanity
open Lp2lc.Active.Util
open Lp2lc.Active.STLC

/--
it is deliberately unconstructable: a fixpoint can hypothetically make it but this is not deliberately provided anywhere

test cases are expected to use the left inverse to demonstrate syntax rules
-/
inductive Symbol where

namespace Symbolic

abbrev I := Free.mkDefault Symbol String

abbrev Typ := AST.Typ I
abbrev Val := AST.Val I
abbrev Trm := AST.Trm I

end Symbolic

open Tests.STLC.Sanity.Symbolic

namespace Val

def idFn : Val :=
  .lam (λ x => .ref x) .primitive

end Val

end Sanity
