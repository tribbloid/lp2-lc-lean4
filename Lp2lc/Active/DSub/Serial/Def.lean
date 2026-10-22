import «Lp2lc».Active.DSub.DSubDef
import «Lp2lc».Active.NatBindings

namespace Lp2lc.Active.DSub

open Lp2lc.Active.Util

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

/-- A source value together with the bindings captured when it was evaluated. -/
abbrev ExeVal := Closure (Val ·)

abbrev ExeBindings := NatBindings ExeVal

end DSub
