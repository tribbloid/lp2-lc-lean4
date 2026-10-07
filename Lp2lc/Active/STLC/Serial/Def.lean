import «Lp2lc».Active.STLC.STLCDef
import «Lp2lc».Active.NatBindings

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

---------------------------- Concrete indexed AST ----------------------------

abbrev AST (n : Nat := 0) (l : Label)  := -- TODO: the label argument is just currying
  Pre.AST { B := String, I := Indices.Serial, index := n } l

abbrev Binder (n : Nat := 0) (l : Label)  :=
  Pre.Binder { B := String, I := Indices.Serial, index := n } l

namespace AST
variable {P : Parameters}

/-- Current STLC subtyping coincides with structural type equality. -/
instance typLE : LE (Pre.AST P .typ) := ⟨Eq⟩

/-- Decides the current structural subtyping relation. -/
@[instance_reducible]
instance typDecidableLE : DecidableLE (Pre.AST P .typ)
  | .TLit, .TLit => isTrue rfl
  | .TLit, .TFn _ _
  | .TFn _ _, .TLit => isFalse (λ equality => nomatch equality)
  | .TFn leftIn leftOut, .TFn rightIn rightOut =>
    match typDecidableLE leftIn rightIn, typDecidableLE leftOut rightOut with
    | isTrue inputEqual, isTrue outputEqual => isTrue (inputEqual ▸ outputEqual ▸ rfl)
    | isFalse notEqual, _ => isFalse (λ equality => notEqual (by cases equality; rfl))
    | _, isFalse notEqual => isFalse (λ equality => notEqual (by cases equality; rfl))

end AST

abbrev Val (n : Nat := 0) := AST n .val
abbrev Trm (n : Nat := 0) := AST n .trm
abbrev Typ (n : Nat := 0) := AST n .typ

namespace Val

def asTrm (self : Val n) : Trm n := .val self

end Val


-- set_option genSizeOf false in
/-- A source value together with the bindings captured when it was evaluated. -/
structure ExeValue : Type 1 where
  n : Nat
  value : Val n
  captured : Bindings ExeValue

abbrev ExeBindings := Bindings ExeValue -- append-only

end STLC
