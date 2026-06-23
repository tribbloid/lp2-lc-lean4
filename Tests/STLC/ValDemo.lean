import «Lp2lc».Active.STLC.STLCDef

namespace Tests.STLC.Sanity
open Lp2lc.Active.Util
open Lp2lc.Active.STLC

/--
it is deliberately unconstructable: FBound can hypothetically make it but this is not deliberately provided anywhere

test cases are expected to use the roundtrip to demonstrate syntax rules
-/
inductive Symbol where

namespace Symbolic

@[reducible] def I : Impl where
  Index := Symbol
  Data := String

abbrev Typ := AST.Typ I
abbrev Val := AST.Val I
abbrev Trm := AST.Trm I

end Symbolic

open Tests.STLC.Sanity.Symbolic

namespace Val

def idFn : Val :=
  .fn (fun x => .ref x) .primitive

end Val

end Sanity
