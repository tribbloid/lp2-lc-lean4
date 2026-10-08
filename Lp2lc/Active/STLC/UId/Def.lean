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

/-- A carrier map retains the bytecode type and FreeOrUnit encoding at both ends. -/
inductive CarrierMap : (source : Parameters) → (target : Parameters) → Type 1 where
| mk {B I1 I2} (mapC : I1 → I2) :
    CarrierMap {B := B, I := IndexEncoding.FreeOrUnit, index := I1}
      {B := B, I := IndexEncoding.FreeOrUnit, index := I2}

private def mapRef {source : Parameters} {P Q} (under : source.Under P)
    (map : CarrierMap P Q) (carrier : source.TRef) : Q.TRef := by
  cases under with
  | same => cases map with
    | mk mapC => exact mapC carrier
  | @lower p2 prev =>
    have recurse := λ {Q} (map : CarrierMap p2 Q) => mapRef prev map carrier
    rcases p2 with ⟨⟨byteCode⟩, encoding, index⟩
    cases map with
    | mk mapC => exact recurse (.mk (λ carrier => mapC (.inl carrier)))

mutual
/-- Maps an AST to a different carrier while retaining its bytecode type and index encoding. -/
@[simp] def AST.recarrier {P Q} {l} (self : Pre.AST P l)
    (map : CarrierMap P Q) (unmapC : Q.TRef → P.TRef) : Pre.AST Q l :=
  match self with
  | .TLit => .TLit
  | .TFn tIn tOut => .TFn (AST.recarrier tIn map unmapC) (AST.recarrier tOut map unmapC)
  | .lit repr => by cases map; exact .lit repr
  | .fn tIn body => .fn (AST.recarrier tIn map unmapC) (Binder.recarrier body map unmapC)
  | .val value => .val (AST.recarrier value map unmapC)
  | .apply fnTerm arg => .apply (AST.recarrier fnTerm map unmapC) (AST.recarrier arg map unmapC)
  | .ref carrier under => .ref (mapRef under map carrier) .same

/-- Maps a binder's outer carriers while preserving its newest slot, bytecode type, and index encoding. -/
@[simp] def Binder.recarrier {P Q} {l} (self : Pre.Binder P l)
    (map : CarrierMap P Q) (unmapC : Q.TRef → P.TRef) : Pre.Binder Q l :=
  match self with
  | .mk body => by
    have recurse := λ {Q} (map : CarrierMap P.Next Q) carrier => AST.recarrier (body carrier) map
    cases map with
    | mk mapC =>
      exact .mk (λ carrier => recurse (.mk (Sum.map mapC id))
        (Sum.map unmapC id carrier) (Sum.map unmapC id))
end
end EnvBase

structure ExeEnv extends base : EnvBase where

end Lp2lc.Active.STLC
