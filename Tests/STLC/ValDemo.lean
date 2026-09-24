import «Lp2lc».Active.STLC.STLCDef

namespace Tests.STLC.Sanity

open Lp2lc.Active.Util Lp2lc.Active.STLC

inductive DemoCarrier where
| root
| extended

namespace Symbolic

/-- The carrier advances to `extended` whenever a binder introduces a body. -/
abbrev I : Parameters :=
  { C := DemoCarrier, B := String, inc := λ _ => .extended }

abbrev Typ := AST.Typ (P := I) .root
abbrev Val := AST.Val (P := I) .root
abbrev Trm := AST.Trm (P := I) .root

end Symbolic

open Symbolic

namespace Val

def idFn : Val :=
  .fn .TLit (.mk (λ proxy => .ref proxy))

end Val

end Tests.STLC.Sanity
