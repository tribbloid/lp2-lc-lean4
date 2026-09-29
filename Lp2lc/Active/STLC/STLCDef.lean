import Std
import «Lp2lc».Active.Util
import «Lp2lc».Active.Parameters

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

def UAST := Type 2

namespace Pre

mutual

/-- A binder introduces the next lexical context for its body. -/
inductive Binder : CtxEmbedding → Label → UAST where
| mk {P : CtxEmbedding} (body : P.TRefNext →
    AST P.Next l) : Binder P l

/-- Source type, value, and term syntax.

`TLit` classifies primitive bytecode values and `TFn` classifies functions.
-/
inductive AST : CtxEmbedding → Label → UAST where
| TLit {P : CtxEmbedding} : AST P .typ -- `AnyVal` in Scala, accepts only primitive values
| lit {P : CtxEmbedding} (repr : P.B) : AST P .val -- most specific type is always `primitive`

| TFn {P : CtxEmbedding} (tIn : AST P .typ) (tOut : AST P .typ) : AST P .typ -- function
| fn {P : CtxEmbedding} (tIn : AST P .typ) (body : Binder P .trm) : AST P .val
    -- most specific type is always `.fn tIn _`

| val {P : CtxEmbedding} (v : AST P .val) : AST P .trm -- AKA literal
| apply {P : CtxEmbedding} (fn : AST P .trm) (arg : AST P .trm) : AST P .trm
    -- fn must be a function that can be applied on arg
-- A lexical reference identifies a binder slot rather than a mutable variable.
| ref {P : CtxEmbedding} {source : P.TIndex} (carrier : P.Proxy source)
    (under : CtxEmbedding.Under {P with index := source} P := by repeat constructor) : AST P .trm
 end

namespace Binder
-- All theorems about Binder should be here, e.g. parametricity, lift relation

/-- Opens a binder body at its declared reference slot. -/
def apply {P : CtxEmbedding} {l : Label}
    (self : Binder P l)
    (carrier : P.TRefNext) :
    AST P.Next l :=
  match self with
  | .mk body =>
    body carrier

end Binder

end Pre
---------------------------- Concrete Parameters ----------------------------

abbrev AST := @Pre.AST

namespace AST

abbrev At (c : CtxEmbedding.DeBruijn.TIndex) : CtxEmbedding := {CtxEmbedding.DeBruijn with index := c}

abbrev Binder (P : CtxEmbedding) (l : Label) := @Pre.Binder P l

abbrev Typ (P : CtxEmbedding) := AST P .typ
abbrev Trm (P : CtxEmbedding) := AST P .trm
abbrev Val (P : CtxEmbedding) := AST P .val

abbrev TLit {P : CtxEmbedding} : AST.Typ P := @Pre.AST.TLit P
abbrev lit {P : CtxEmbedding} (repr : P.B) : AST.Val P := @Pre.AST.lit P repr
abbrev TFn {P : CtxEmbedding} (tIn tOut : AST.Typ P) : AST.Typ P :=
  @Pre.AST.TFn P tIn tOut
abbrev fn {P : CtxEmbedding} (tIn : AST.Typ P) (body : AST.Binder P .trm) : AST.Val P :=
  @Pre.AST.fn P tIn body
abbrev val {P : CtxEmbedding} (v : AST.Val P) : AST.Trm P := @Pre.AST.val P v
abbrev apply {P : CtxEmbedding} (fn arg : AST.Trm P) : AST.Trm P := @Pre.AST.apply P fn arg
abbrev ref {P : CtxEmbedding} {source : P.TIndex} (carrier : P.Proxy source)
    (under : CtxEmbedding.Under {P with index := source} P := by repeat constructor) : AST.Trm P :=
  @Pre.AST.ref P source carrier under

/-- Current STLC subtyping coincides with structural type equality. -/
instance typLE {P : CtxEmbedding} : LE (AST.Typ P) := ⟨Eq⟩

/-- Decides the current structural subtyping relation. -/
@[instance_reducible]
instance typDecidableLE {P : CtxEmbedding} : DecidableLE (AST.Typ P)
  | .TLit, .TLit => isTrue rfl
  | .TLit, .TFn _ _
  | .TFn _ _, .TLit => isFalse (λ equality => nomatch equality)
  | .TFn leftIn leftOut, .TFn rightIn rightOut =>
    match typDecidableLE leftIn rightIn, typDecidableLE leftOut rightOut with
    | isTrue inputEqual, isTrue outputEqual => isTrue (inputEqual ▸ outputEqual ▸ rfl)
    | isFalse notEqual, _ => isFalse (λ equality => notEqual (by cases equality; rfl))
    | _, isFalse notEqual => isFalse (λ equality => notEqual (by cases equality; rfl))

namespace Val

def asTrm {P : CtxEmbedding} (self : AST.Val P) : AST.Trm P := .val self

end Val

end AST

end Lp2lc.Active.STLC
