import «Lp2lc».Active.STLC.STLCDef

namespace Tests.STLC_Eval.Sanity

open Lp2lc.Active.Util
open Lp2lc.Active.STLC

inductive Symbol

namespace Symbolic

@[reducible] def I : Free where
  Index := Symbol
  Reify := Unit
  Data := String

instance : I.Free.CanReify where
  payload := ()

abbrev Typ := AST.Typ I
abbrev Val := AST.Val I
abbrev Trm := AST.Trm I

end Symbolic

open Symbolic

namespace Val

def vFalse : Val :=
  .primitive "false"

def vTrue : Val :=
  .primitive "true"

def idFn : Val :=
  .fn (fun ref => .ref ref) .primitive

end Val

end Sanity
