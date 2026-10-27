import «Lp2lc».Active.DTLC.DTLCDef
import «Lp2lc».Active.NatBindings

namespace Lp2lc.Active.DTLC

open Lp2lc.Active.Util

---------------------------- Concrete indexed AST ----------------------------

abbrev AST (n : Nat := 0) (l : Label) :=
  Pre.AST { B := String, I := IndexEncoding.Serial, index := ⟨n⟩ } l

abbrev Binder (n : Nat := 0) (l : Label) :=
  Pre.Binder { B := String, I := IndexEncoding.Serial, index := ⟨n⟩ } l

abbrev Val (n : Nat := 0) := AST n .val
abbrev Trm (n : Nat := 0) := AST n .trm
abbrev Typ (n : Nat := 0) := AST n .typ

namespace Val

def asTrm (self : Val n) : Trm n := .val self

end Val

/-- A source value together with its captured runtime bindings. -/
abbrev ExeVal := Closure (Val ·)

abbrev ExeBindings := NatBindings ExeVal

end DTLC
