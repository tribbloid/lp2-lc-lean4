import «Lp2lc».Active.STLC.STLCDef

namespace Tests.STLC.Sanity
open Lp2lc.Active.Util
open Lp2lc.Active.STLC
open Lp2lc.Next.Util

/--
it is deliberately unconstructable: a fixpoint can hypothetically make it but this is not deliberately provided anywhere

test cases are expected to use the left inverse to demonstrate syntax rules
-/
inductive Symbol where

namespace Symbolic

abbrev I : Parameters := { C := Symbol, D := String }

abbrev Typ := AST.Typ I
abbrev Val := AST.Val I
abbrev Trm := AST.Trm I

end Symbolic

open Tests.STLC.Sanity.Symbolic

namespace Val

def idFn : Val :=
  .lam (λ x => .ref (.inl x)) .primitive

end Val

end Sanity
