import «Lp2lc».Active.STLC.UId.Def

namespace Lp2lc.Active.STLC.EnvBase
open Lp2lc.Active.Util

/-- A carrier map retains the bytecode type and FreeOrUnit encoding at both ends. -/
inductive CarrierMap : (source : Parameters) → (target : Parameters) → Type 1 where
| mk {B I1 I2} (mapC : I1 → I2) :
    CarrierMap {B := B, I := IndexEncoding.FreeOrUnit, index := I1}
      {B := B, I := IndexEncoding.FreeOrUnit, index := I2}

/-- Resolves an ancestor reference into the target carrier before shared receipt lookup. -/
def mapRef {source : Parameters} {P Q} (under : source.Under P)
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
@[simp] def AST.recarrier {P Q l} (self : Pre.AST P l) (map : CarrierMap P Q) : Pre.AST Q l :=
  match self with
  | .TLit => .TLit
  | .TFn tIn tOut => .TFn (AST.recarrier tIn map) (AST.recarrier tOut map)
  | .lit repr => by cases map; exact .lit repr
  | .fn tIn body => .fn (AST.recarrier tIn map) (Binder.recarrier body map)
  | .val value => .val (AST.recarrier value map)
  | .apply fnTerm arg => .apply (AST.recarrier fnTerm map) (AST.recarrier arg map)
  | .ref carrier under => .ref (mapRef under map carrier) .same

/-- Maps a binder's outer references while preserving its newest structural slot.

Opens the source callback only at `.inr ()` and maps that fixed body using `Sum.map mapC id`.
The rebuilt callback returns the mapped body for every input. Preserving the right `Unit` summand
keeps the newest slot available for later substitution and makes a backward carrier map unnecessary.
-/
@[simp] def Binder.recarrier {P Q l} (self : Pre.Binder P l) (map : CarrierMap P Q) : Pre.Binder Q l :=
  match self, map with
  | .mk body, .mk mapC => .mk (λ _ => AST.recarrier (body (.inr ())) (.mk (Sum.map mapC id)))
end

/-- Instantiates a UId binder by substituting a receipt into its canonical structural body.

After opening only at `.inr ()`, the reference map sends `.inl outer` to `outer` and `.inr ()` to
`carrier`, returning syntax in the original context. Beneath nested binders, carrier transport
preserves their newest slots while substituting references to this outer slot.

Use `EnvBase.Binder.apply` to instantiate UId syntax. Its call to the shared raw `Pre.Binder.apply`
supplies `.inr ()` solely to obtain the body in the extended context.
-/
def Binder.apply {this : EnvBase} {l} (self : this.Binder l)
    (carrier : this.UId) : this.AST l :=
  AST.recarrier (Pre.Binder.apply self (.inr ())) (.mk (Sum.elim id (λ _ => carrier)))

end Lp2lc.Active.STLC.EnvBase
