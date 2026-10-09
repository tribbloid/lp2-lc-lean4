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

abbrev TypOrVal := this.Typ ⊕ this.Val

end

def Val.asTrm {this : EnvBase} (v : this.Val) : this.Trm := .val v
end EnvBase

/-- One read-only receipt view shared by compile-time type lookup and runtime value lookup. -/
structure UIdRefs extends base : EnvBase where
  uid2both : KVRefs UId (base.TypOrVal)

end Lp2lc.Active.STLC
