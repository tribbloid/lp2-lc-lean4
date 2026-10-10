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

/-- A binder with uniform receipt substitution through its canonical structural body.

For outer carrier `C`, the next context is `C ⊕ Unit`. UId opens only the contractible right
summand at `.inr ()`, then substitutes receipts into that fixed body structurally, including beneath
nested binders. The stored callback is internal construction data and must not be consumed as a
nonuniform function. Instantiate UId syntax with `Root.Binder.apply`.
-/
abbrev Binder (l : Label) (I : Type := this.UId) := Pre.Binder (this.P I) l
abbrev Val := this.AST .val
abbrev Trm := this.AST .trm
abbrev Typ := this.AST .typ

end

def Val.asTrm {this : Root} (v : this.Val) : this.Trm := .val v
end Root

end Lp2lc.Active.STLC
