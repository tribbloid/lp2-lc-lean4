import «Lp2lc».Active.STLC.STLCDef

namespace Tests.STLC.Sanity

open Lp2lc.Active.STLC
open Lp2lc.Active.Util

def bFalse := "false"

def bTrue := "true"

namespace Trm.FreeCapture

/-- A symbolic outer-context slot used by the syntax-only capture examples. -/
def freeSlot : p0.TRef := .only

end Trm.FreeCapture

/-- Supplies literal values and an outer reference for the generic syntax demos. -/
class Demo (P : Parameters) where
  bFalse : P.B
  bTrue : P.B
  freeSlot : P.TRef

instance serialDemo : Demo p0 := ⟨bFalse, bTrue, Trm.FreeCapture.freeSlot⟩

namespace Val
variable (P : Parameters := p0)

def idFn [Demo P] : Pre.AST P .val :=
  .fn .TLit (.mk (λ proxy => .ref proxy .same))

section generalization

example : (idFn : AST 0 .val) = .fn .TLit (.mk (λ proxy => .ref proxy .same)) := rfl

example {P : Parameters} [Demo P] :
    idFn P = .fn .TLit (.mk (λ proxy => .ref proxy .same)) := rfl

end generalization

end Val

end Tests.STLC.Sanity
