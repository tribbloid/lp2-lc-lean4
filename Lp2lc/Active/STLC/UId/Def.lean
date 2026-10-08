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

section variable {this : EnvBase}
def Val.asTrm (v : this.Val) : this.Trm := .val v

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
/-- Maps an AST to a different carrier. -/
@[simp]
def AST.recarrier {P : Parameters} {I2 : Type} {l} (self : Pre.AST P l)
    (mapC : P.TRef → I2) (unmapC : I2 → P.TRef) (encoding : P.I = IndexEncoding.FreeOrUnit) :
    Pre.AST {P with I := IndexEncoding.FreeOrUnit, index := I2} l :=
  match self with
  | .TLit => .TLit
  | .TFn tIn tOut => .TFn (AST.recarrier tIn mapC unmapC encoding) (AST.recarrier tOut mapC unmapC encoding)
  | .lit repr => .lit repr
  | .fn tIn body => .fn (AST.recarrier tIn mapC unmapC encoding) (Binder.recarrier body mapC unmapC encoding)
  | .val value => .val (AST.recarrier value mapC unmapC encoding)
  | .apply fnTerm arg => .apply (AST.recarrier fnTerm mapC unmapC encoding) (AST.recarrier arg mapC unmapC encoding)
  | .ref carrier under => .ref (mapC (embedRef under carrier encoding)) .same

/-- Maps the outer carriers of a binder while preserving its newest slot. -/
@[simp]
def Binder.recarrier {P : Parameters} {I2 : Type} {l} (self : Pre.Binder P l)
    (mapC : P.TRef → I2) (unmapC : I2 → P.TRef) (encoding : P.I = IndexEncoding.FreeOrUnit) :
    Pre.Binder {P with I := IndexEncoding.FreeOrUnit, index := I2} l :=
  match self with
  | .mk body => by
    have recurse := λ carrier => AST.recarrier (I2 := I2 ⊕ Unit) (body carrier)
    rcases P with ⟨byteCode, encoding2, index⟩
    cases encoding
    exact .mk (λ carrier => recurse (Sum.map unmapC id carrier) (Sum.map mapC id) (Sum.map unmapC id) rfl)
end
end
end EnvBase

structure ExeEnv extends base : EnvBase where

end Lp2lc.Active.STLC
