import Std
import «Lp2lc».Active.Util
import «Lp2lc».Active.Parameters

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

def UAST := Type 2

mutual

/-- A binder introduces the next lexical context for its body. -/
inductive Binder : Parameters → Label → UAST where
| mk {P : Parameters} (body : P.TRefNext → AST P.Next l) : Binder P l

/-- Source type, value, and term syntax.

`TLit` classifies primitive bytecode values and `TFn` classifies functions.
-/
inductive AST : Parameters → Label → UAST where
| TLit {P : Parameters} : AST P .typ -- `AnyVal` in Scala, accepts only primitive values
| lit {P : Parameters} (repr : P.B) : AST P .val -- most specific type is always `primitive`

| TFn {P : Parameters} (tIn : AST P .typ) (tOut : AST P .typ) : AST P .typ -- function
| fn {P : Parameters} (tIn : AST P .typ) (body : Binder P .trm) : AST P .val
    -- most specific type is always `.fn tIn _`

| val {P : Parameters} (v : AST P .val) : AST P .trm -- AKA literal
| apply {P : Parameters} (fn : AST P .trm) (arg : AST P .trm) : AST P .trm
    -- fn must be a function that can be applied on arg
-- A lexical reference identifies a binder slot rather than a mutable variable.
| ref {P : Parameters} (carrier : P.TRef) : AST P .trm
 end

namespace Binder
-- All theorems about Binder should be here, e.g. parametricity, lift relation

/-- Opens a binder body with the supplied reference receipt. -/
def apply {P : Parameters} {l : Label} (self : Binder P l)
    (carrier : P.TRefNext) : AST P.Next l :=
  match self with
  | .mk body => body carrier

end Binder

---------------------------- Concrete Parameters ----------------------------

namespace AST

abbrev Typ (P : Parameters) := AST P .typ
abbrev Trm (P : Parameters) := AST P .trm
abbrev Val (P : Parameters) := AST P .val

/-- Current STLC subtyping coincides with structural type equality. -/
instance typLE {P : Parameters} : LE (AST.Typ P) := ⟨Eq⟩

/-- Decides the current structural subtyping relation. -/
@[instance_reducible]
instance typDecidableLE {P : Parameters} : DecidableLE (AST.Typ P)
  | .TLit, .TLit => isTrue rfl
  | .TLit, .TFn _ _
  | .TFn _ _, .TLit => isFalse (λ equality => nomatch equality)
  | .TFn leftIn leftOut, .TFn rightIn rightOut =>
    match typDecidableLE leftIn rightIn, typDecidableLE leftOut rightOut with
    | isTrue inputEqual, isTrue outputEqual => isTrue (inputEqual ▸ outputEqual ▸ rfl)
    | isFalse notEqual, _ => isFalse (λ equality => notEqual (by cases equality; rfl))
    | _, isFalse notEqual => isFalse (λ equality => notEqual (by cases equality; rfl))

namespace Val

def asTrm {P : Parameters} (self : AST.Val P) : AST.Trm P := .val self

end Val

end AST

end Lp2lc.Active.STLC
