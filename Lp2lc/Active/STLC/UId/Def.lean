import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

structure EnvBase where
  UId : Type -- PHOAS carrier for anything, but not always the AST index (which uses FreeOrUnit encoding)

namespace EnvBase
section variable (this : EnvBase) (I : Type := this.UId)

-- FreeOrUnit is chosen to make verifying binder uniformity easier.
abbrev P : Parameters := {B := String, I := .FreeOrUnit, index := I}

abbrev AST (l : Label) := Pre.AST this.P l

abbrev Binder (l : Label) := Pre.Binder this.P l

abbrev Val := AST this .val
abbrev Trm := AST this .trm
abbrev Typ := AST this .typ

end section

section variable {this : EnvBase}

def Val.asTrm {this : EnvBase} (v : this.Val) : this.Trm := .val v

/-- Maps an AST to a different carrier. -/
@[simp]
def AST.recarrier {l} (self : this.AST l) (I2: Type) : this.AST I2 l :=
  match self with
  | .primitive => .primitive
  | .fn tIn tOut =>
    .fn (tIn.recarrier mapC mapB) (tOut.recarrier mapC mapB)
  | .val value => .val (value.recarrier mapC mapB)
  | .apply fnTerm arg =>
    .apply (fnTerm.recarrier mapC mapB) (arg.recarrier mapC mapB)
  | .ref receipt => .ref (mapC receipt)
  | .lit repr => .lit (mapB repr)
  | .lam body tIn =>
    .lam (body.recarrier mapC mapB) (tIn.recarrier mapC mapB)

/-- Maps the outer carriers of a binder while preserving its newest slot. -/
@[simp]
def Binder.recarrier {l} (self : this.Binder l) (I2 : Type) : this.Binder I2 l :=
  match self with
  | .mk body =>
    .mk (body.recarrier
      (λ receipt =>
        match receipt with
        | .inl outer => .inl (mapC outer)
        | .inr () => .inr ())
      mapB)

end section
end EnvBase

section variable (this : EnvBase)
structure ExeEnv extends base : EnvBase where


end



end STLC
