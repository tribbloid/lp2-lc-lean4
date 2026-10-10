import «Lp2lc».Active.STLC.STLCDef

/-!
# UId syntax with structural binder slots

`Root` fixes the carrier of free reference receipts. Its syntax uses `String` literals and the
`FreeOrUnit` encoding, with separate `.typ`, `.val`, and `.trm` families in the shared `Pre.AST`.

For an outer carrier `C`, a binder extends references to `C ⊕ Unit`: `.inl outer` retains an outer
reference, and `.inr ()` denotes the newest bound slot. Nested binders repeat this extension, giving
`(C ⊕ Unit) ⊕ Unit` at the next depth. References may retain an earlier source context through an
`Under` witness; carrier transport maps them into the target context's reference carrier.
-/

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util

structure Root where
  /-- Free reference receipt carrier, extended with a structural `Unit` slot beneath each binder. -/
  UId : Type

namespace Root

/-- Syntax parameters for carrier `I`, initially `this.UId`, with `String` literals and `FreeOrUnit`.

UId binders are opened only at `.inr ()`; receipts replace that slot by structural substitution.
-/
abbrev P (this : Root) (I : Type := this.UId) : Parameters :=
  {B := String, I := IndexEncoding.FreeOrUnit, index := I}

section variable (this : Root)
abbrev AST (l : Label) (I : Type := this.UId) := Pre.AST (this.P I) l

/-- A shared functional binder interpreted through its canonical structural body.

The stored callback has type `P.Next.TRef → Pre.AST P.Next l`. For outer carrier `C`, its input
carrier is `C ⊕ Unit`, but UId operations contract the allowed opening to the right `Unit` summand:
the sole argument supplied is `.inr ()`. The syntax consumed by these operations is therefore the
fixed body `body (.inr ())`; this convention is repeated beneath nested binders.

Opening the callback at `.inl receipt` could expose nonuniform behavior. Instead, UId substitutes
that receipt into the canonical body's bound slot. The callback never receives the receipt being
substituted, so these operations do not require uniformity across its other possible inputs.

Under this opening contract, a binder represents its fixed canonical body together with structural
substitution. The shared function type still permits arbitrary callbacks; equivalence here concerns
canonical bodies and structural substitution, not equality at every callback input.
-/
abbrev Binder (l : Label) (I : Type := this.UId) := Pre.Binder (this.P I) l
abbrev Val := this.AST .val
abbrev Trm := this.AST .trm
abbrev Typ := this.AST .typ

end

def Val.asTrm {this : Root} (v : this.Val) : this.Trm := .val v
end Root

end Lp2lc.Active.STLC
