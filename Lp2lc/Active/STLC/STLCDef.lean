import Std
import «Lp2lc».Active.Util
import «Lp2lc».Active.Parameters

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

def UAST := Type 2

/-
Unreified AST with parametric carrier

Rule: this is an internal API, actual language should use AST/Binder under STLC namespace
-/
namespace Pre

mutual

/-- A binder introduces the next lexical context for its body. -/
inductive Binder : Parameters → Label → UAST where
| mk {P} (body : P.I.getTRef P.Next.index → AST P.Next l) : Binder P l

/-- Source type, value, and term syntax.

`TLit` classifies primitive bytecode values and `TFn` classifies functions.
-/
inductive AST : Parameters → Label → UAST where
| TLit {P} : AST P .typ -- `AnyVal` in Scala, accepts only primitive values
| lit {P} (repr : P.B) : AST P .val -- most specific type is always `primitive`

| TFn {P} (tIn : AST P .typ) (tOut : AST P .typ) : AST P .typ -- function
| fn {P} (tIn : AST P .typ) (body : Binder P.Next .trm) : AST P .val
    -- most specific type is always `.fn tIn _`

| val {P} (v : AST P .val) : AST P .trm -- AKA literal
| apply {P} (fn : AST P .trm) (arg : AST P .trm) : AST P .trm
    -- fn must be a function that can be applied on arg
-- A lexical reference retains its source context and a witness reaching the current context.
| ref {P} {lower : P.I.Index} (carrier : P.I.getTRef lower)
    (under : ({P with index := lower}).Under P) : AST P .trm
 end

namespace Binder
-- All theorems about Binder should be here, e.g. parametricity, lift relation

/-- Opens a binder body with the supplied reference receipt. -/
def apply {P : Parameters} {l : Label} (self : Binder P l)
    (carrier : P.I.getTRef P.Next.index) : AST P.Next l :=
  match self with
  | .mk body => body carrier

end Binder

end Pre
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

end Lp2lc.Active.STLC
