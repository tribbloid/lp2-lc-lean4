import «Lp2lc».Active.STLC.STLCDef

/-!
# UId syntax with structural binder slots

`EnvBase` fixes the carrier of free reference receipts. Its syntax uses `String` literals and the
`FreeOrUnit` encoding, with separate `.typ`, `.val`, and `.trm` families in the shared `Pre.AST`.

For an outer carrier `C`, a binder extends references to `C ⊕ Unit`: `.inl outer` retains an outer
reference, and `.inr ()` denotes the newest bound slot. Nested binders repeat this extension, giving
`(C ⊕ Unit) ⊕ Unit` at the next depth. References may retain an earlier source context through an
`Under` witness; carrier transport maps them into the target context's reference carrier.
-/

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util

structure EnvBase where
  /-- Free reference receipt carrier, extended with a structural `Unit` slot beneath each binder. -/
  UId : Type

namespace EnvBase

/-- Syntax parameters for carrier `I`, initially `this.UId`, with `String` literals and `FreeOrUnit`.

UId binders are opened only at `.inr ()`; receipts replace that slot by structural substitution.
-/
abbrev P (this : EnvBase) (I : Type := this.UId) : Parameters :=
  {B := String, I := IndexEncoding.FreeOrUnit, index := I}

section variable (this : EnvBase)
abbrev AST (l : Label) (I : Type := this.UId) := Pre.AST (this.P I) l

/-- A shared functional binder interpreted through its canonical structural body.

The stored callback has type `P.Next.TRef → Pre.AST P.Next l`. For outer carrier `C`, its input
carrier is `C ⊕ Unit`, but UId operations contract the allowed opening to the right `Unit` summand:
the sole argument supplied is `.inr ()`. The syntax consumed by these operations is therefore the
fixed body `body (.inr ())`; this convention is repeated beneath nested binders.

Opening the callback at `.inl receipt` could expose nonuniform behavior. Instead, UId substitutes
that receipt into the canonical body's bound slot. The callback never receives the receipt being
substituted, so these operations do not require uniformity across its other possible inputs.

Under this opening contract, the binder has the same operational role as the stored first-order body
in `STLCv4_FreeOrUnit`. The shared function type still permits arbitrary callbacks; equivalence here
concerns canonical bodies and structural substitution, not equality at every callback input.
-/
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
end EnvBase

/-- One read-only receipt view shared by compile-time type lookup and runtime value lookup. -/
structure UIdRefs extends base : EnvBase where
  uid2any : KVRefs UId (base.Val ⊕ base.Typ)

end Lp2lc.Active.STLC
