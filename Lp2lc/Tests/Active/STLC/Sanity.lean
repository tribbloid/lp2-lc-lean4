import «Lp2lc».Active.STLC.Proof

namespace Lp2lc.Active.STLC.Tests

open Lp2lc.Active.STLC

namespace Typ

def base_typ : Closed Typ :=
  fun _ => .base

def mono_arrow_typ : Closed Typ :=
  fun _ => .monoArrow .base .base

#guard
  let _ : base_typ Unit = .base := rfl
  true

#guard
  let _ : mono_arrow_typ Unit = (.base :=> .base) := rfl
  true

end Typ

namespace Trm

def trm1 (Index : Type) : Trm Index :=
 .literal "" .base

def trm2 : Closed Trm := trm1 -- eta-expansion happens automatically

def trm3 (Index : Type) : Trm Index :=
 trm2 Index

def literal_trm : Closed Trm :=
  fun _ => .literal "3" .base

def mono_fn_trm : Closed Trm :=
  fun _ => .monoFn (fun arg => .var arg .base) .base .base

def mono_apply_trm : Closed Trm :=
  fun Index => .monoApply (mono_fn_trm Index) (literal_trm Index)

#guard
  let _ : literal_trm Unit = .literal "3" .base := rfl
  true

#guard
  let _ : mono_fn_trm Unit = .monoFn (fun arg => .var arg .base) .base .base := rfl
  true

#guard
  let _ : mono_apply_trm Unit = .monoApply (mono_fn_trm Unit) (literal_trm Unit) := rfl
  true

end Trm

end Tests
