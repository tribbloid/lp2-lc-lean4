import «Lp2lc».Active.STLC_minimal.STLCDef
import «Lp2lc».Active.NatBindings

namespace Lp2lc.Active.STLC_minimal

open Lp2lc.Active.Util

abbrev AST (n : Nat := 0) (l : Label)  :=
  Pre.AST { B := String, I := IndexEncoding.Serial, index := ⟨n⟩ } l

abbrev Binder (n : Nat := 0) (l : Label)  :=
  Pre.Binder { B := String, I := IndexEncoding.Serial, index := ⟨n⟩ } l

abbrev Val (n : Nat := 0) := AST n .val
abbrev Trm (n : Nat := 0) := AST n .trm
abbrev Typ (n : Nat := 0) := AST n .typ

namespace Val

def asTrm (self : Val n) : Trm n := .val self

instance : Coe (Val n) (Trm n) := ⟨asTrm⟩

instance (self : Val n) : CoeT (Val n) self (Trm n) := ⟨Coe.coe self⟩

end Val

abbrev ExeVal := Closure (Val ·)

abbrev ExeBindings := NatBindings ExeVal

end STLC_minimal
