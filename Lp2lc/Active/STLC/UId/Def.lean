import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util

structure EnvBase where
  UId : Type -- PHOAS carrier for anything, but not always the AST index (which uses FreeOrUnit encoding)

namespace EnvBase

-- FreeOrUnit is chosen to make verifying binder uniformity easier.
abbrev P (this : EnvBase) (I : Type := this.UId) : Parameters :=
  {B := String, I := IndexEncoding.FreeOrUnit, index := I}

section variable (this : EnvBase)
abbrev AST (l : Label) (I : Type := this.UId) := Pre.AST (this.P I) l
abbrev Binder (l : Label) (I : Type := this.UId) := Pre.Binder (this.P I) l
abbrev Val := this.AST .val
abbrev Trm := this.AST .trm
abbrev Typ := this.AST .typ
end

def Val.asTrm {this : EnvBase} (v : this.Val) : this.Trm := .val v

private def embedRef {source target : Parameters}
    (under : source.Under target) (carrier : source.TRef)
    (encoding : target.I = IndexEncoding.FreeOrUnit) : target.TRef := by
  cases under with
  | same => exact carrier
  | lower prev =>
    have previous := embedRef prev carrier
    rename_i p2
    rcases p2 with ⟨byteCode, encoding2, index⟩
    dsimp [Parameters.Next] at encoding
    cases encoding
    exact .inl (previous rfl)

mutual
@[simp] private def mapAST {P} {I2} {l} (enc : P.I = IndexEncoding.FreeOrUnit)
    (self : Pre.AST P l) (mapC : P.TRef → I2) (unmapC : I2 → P.TRef) :
    Pre.AST {P with I := IndexEncoding.FreeOrUnit, index := I2} l :=
  match self with
  | .TLit => .TLit
  | .TFn tIn tOut => .TFn (mapAST enc tIn mapC unmapC) (mapAST enc tOut mapC unmapC)
  | .lit repr => .lit repr
  | .fn tIn body => .fn (mapAST enc tIn mapC unmapC) (mapBinder enc body mapC unmapC)
  | .val value => .val (mapAST enc value mapC unmapC)
  | .apply fnTerm arg => .apply (mapAST enc fnTerm mapC unmapC) (mapAST enc arg mapC unmapC)
  | .ref carrier under => .ref (mapC (embedRef under carrier enc)) .same

@[simp] private def mapBinder {P} {I2} {l} (enc : P.I = IndexEncoding.FreeOrUnit)
    (self : Pre.Binder P l) (mapC : P.TRef → I2) (unmapC : I2 → P.TRef) :
    Pre.Binder {P with I := IndexEncoding.FreeOrUnit, index := I2} l :=
  match self with
  | .mk body => by
    have recurse := λ carrier enc => mapAST (I2 := I2 ⊕ Unit) enc (body carrier)
    rcases P with ⟨byteCode, enc2, index⟩
    cases enc
    exact .mk (λ carrier => recurse (Sum.map unmapC id carrier) rfl (Sum.map mapC id) (Sum.map unmapC id))
end

/-- Maps an AST to a different carrier with fixed String bytecode and FreeOrUnit encoding. -/
@[simp] abbrev AST.recarrier {I1 I2 : Type} {l} :=
  @mapAST (P ⟨I1⟩) I2 l rfl

/-- Maps a binder's outer carriers while preserving its newest slot and fixed encoding. -/
@[simp] abbrev Binder.recarrier {I1 I2 : Type} {l} :=
  @mapBinder (P ⟨I1⟩) I2 l rfl
end EnvBase

structure ExeEnv extends base : EnvBase where

end Lp2lc.Active.STLC
