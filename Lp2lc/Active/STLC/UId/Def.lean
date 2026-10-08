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

private def embedRef {source target : Parameters} {B I1 : Type}
    (under : source.Under target) (same : target = {B := B, I := IndexEncoding.FreeOrUnit, index := I1})
    (carrier : source.TRef) : I1 := by
  cases under with
  | same => cases same; exact carrier
  | @lower p2 prev =>
    have recurse := λ {B I1} => embedRef (B := B) (I1 := I1) prev
    rcases p2 with ⟨byteCode, encoding, index⟩
    cases same
    exact .inl (recurse rfl carrier)

mutual
@[simp] private def mapAST {P} {I1 I2 : Type} {l}
    (same : P = {P with I := IndexEncoding.FreeOrUnit, index := I1})
    (self : Pre.AST P l) (mapC : I1 → I2) (unmapC : I2 → I1) :
    Pre.AST {P with I := IndexEncoding.FreeOrUnit, index := I2} l :=
  match self with
  | .TLit => .TLit
  | .TFn tIn tOut => .TFn (mapAST same tIn mapC unmapC) (mapAST same tOut mapC unmapC)
  | .lit repr => .lit repr
  | .fn tIn body => .fn (mapAST same tIn mapC unmapC) (mapBinder same body mapC unmapC)
  | .val value => .val (mapAST same value mapC unmapC)
  | .apply fnTerm arg => .apply (mapAST same fnTerm mapC unmapC) (mapAST same arg mapC unmapC)
  | .ref carrier under => .ref (mapC (embedRef under same carrier)) .same

@[simp] private def mapBinder {P} {I1 I2 : Type} {l}
    (same : P = {P with I := IndexEncoding.FreeOrUnit, index := I1})
    (self : Pre.Binder P l) (mapC : I1 → I2) (unmapC : I2 → I1) :
    Pre.Binder {P with I := IndexEncoding.FreeOrUnit, index := I2} l :=
  match self with
  | .mk body => by
    have recurse := λ same carrier => mapAST (I1 := I1 ⊕ Unit) (I2 := I2 ⊕ Unit) same (body carrier)
    rcases P with ⟨byteCode, encoding, index⟩
    cases same
    exact .mk (λ carrier => recurse rfl (Sum.map unmapC id carrier) (Sum.map mapC id) (Sum.map unmapC id))
end

section variable {B I1 I2 : Type} {l}
/-- Maps an AST to a different carrier while retaining its bytecode type and index encoding. -/
@[simp] abbrev AST.recarrier :=
  @mapAST {B := B, I := IndexEncoding.FreeOrUnit, index := I1} I1 I2 l rfl

/-- Maps a binder's outer carriers while preserving its newest slot, bytecode type, and index encoding. -/
@[simp] abbrev Binder.recarrier :=
  @mapBinder {B := B, I := IndexEncoding.FreeOrUnit, index := I1} I1 I2 l rfl
end
end EnvBase

structure ExeEnv extends base : EnvBase where

end Lp2lc.Active.STLC
