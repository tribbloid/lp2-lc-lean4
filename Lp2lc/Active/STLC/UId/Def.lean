import «Lp2lc».Active.STLC.STLCDef
import «Lp2lc».Active.NatBindings

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

structure EnvBase where
  I : Indices.FreeOrUnit -- chosen to make verifying binder uniformity easier

namespace EnvBase
section variable (this : EnvBase)

def P : Parameters := {B := String, I := this.I, index := this.UId}

def UId := this.I.Index

abbrev AST (l : Label) := Pre.AST P l

abbrev Binder (l : Label) := Pre.Binder P l

abbrev Val := AST .val
abbrev Trm := AST .trm
abbrev Typ := AST .typ

def Val.asTrm (v : Val) : Trm := .val self

end
end EnvBase

end STLC
