import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

structure EnvBase where
  UId : Type

namespace EnvBase
section variable (this : EnvBase)

-- FreeOrUnit is chosen to make verifying binder uniformity easier.
abbrev P0 : Parameters := {B := String, I := .FreeOrUnit, index := this.UId}

-- def P1 := this.P0.Next

abbrev AST (l : Label) := Pre.AST this.P0 l

abbrev Binder (l : Label) := Pre.Binder this.P0 l

abbrev Val := this.AST .val
abbrev Trm := this.AST .trm
abbrev Typ := this.AST .typ

def Val.asTrm {this : EnvBase} (v : this.Val) : this.Trm := .val v

end
end EnvBase


end STLC
