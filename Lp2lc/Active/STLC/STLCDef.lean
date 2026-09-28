import Std
import «Lp2lc».Active.Util

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

def UAST := Type 2

namespace Pre

mutual

/-- A binder introduces the next lexical context for its body. -/
inductive Binder {P : Parameters} : P.Index → Label → UAST where
| mk (body : P.Proxy c → AST (P.inc c) l) : Binder c l

/-- Source type, value, and term syntax.

`TLit` classifies primitive bytecode values and `TFn` classifies functions.
-/
inductive AST {P : Parameters} : P.Index → Label → UAST where
| TLit : AST c .typ -- `AnyVal` in Scala, accepts only primitive values
| lit (repr : P.B) : AST c .val -- most specific type is always `primitive`

| TFn (tIn : AST c .typ) (tOut : AST c .typ) : AST c .typ -- function
| fn (tIn : AST c .typ) (body : Binder c .trm) : AST c .val -- most specific type is always `.fn tIn _`

| val (v : AST c .val) : AST c .trm -- AKA literal
| apply (fn : AST c .trm) (arg : AST c .trm) : AST c .trm -- fn must be a function that can be applied on arg
-- A lexical reference identifies a binder slot rather than a mutable variable.
| ref (carrier : P.Proxy c)
    (lesser : P.Lesser (P.inc c) target := by repeat constructor) : AST target .trm
 end

namespace Binder
-- All theorems about Binder should be here, e.g. parametricity, lift relation

/-- Opens a binder body at its declared reference slot. -/
def apply {P : Parameters} {c : P.Index} {l : Label}
    (self : Binder c l) (carrier : P.Proxy c) : AST (P.inc c) l :=
  match self with
  | .mk body =>
    body carrier

end Binder

end Pre
--------------------------- Locking down Parameters -------------------------

abbrev DeBruijn : Parameters := {Index := Nat, B := String, inc := λ v => v + 1 }

abbrev AST := @Pre.AST DeBruijn

namespace AST

abbrev Binder (c : DeBruijn.Index) (l : Label) := @Pre.Binder DeBruijn c l

abbrev Typ (c : DeBruijn.Index) := AST c .typ
abbrev Trm (c : DeBruijn.Index) := AST c .trm
abbrev Val (c : DeBruijn.Index) := AST c .val

abbrev TLit {c : DeBruijn.Index} : AST c .typ := @Pre.AST.TLit DeBruijn c
abbrev lit {c : DeBruijn.Index} (repr : DeBruijn.B) : AST c .val := @Pre.AST.lit DeBruijn c repr
abbrev TFn {c : DeBruijn.Index} (tIn tOut : AST.Typ c) : AST c .typ :=
  @Pre.AST.TFn DeBruijn c tIn tOut
abbrev fn {c : DeBruijn.Index} (tIn : AST.Typ c) (body : AST.Binder c .trm) : AST c .val :=
  @Pre.AST.fn DeBruijn c tIn body
abbrev val {c : DeBruijn.Index} (v : AST.Val c) : AST c .trm := @Pre.AST.val DeBruijn c v
abbrev apply {c : DeBruijn.Index} (fn arg : AST.Trm c) : AST c .trm := @Pre.AST.apply DeBruijn c fn arg
abbrev ref {c target : DeBruijn.Index} (carrier : DeBruijn.Proxy c)
    (lesser : DeBruijn.Lesser (DeBruijn.inc c) target := by repeat constructor) : AST target .trm :=
  @Pre.AST.ref DeBruijn c target carrier lesser

/-- Current STLC subtyping coincides with structural type equality. -/
instance typLE (c : DeBruijn.Index) : LE (AST.Typ c) := ⟨Eq⟩

/-- Decides the current structural subtyping relation. -/
@[instance_reducible]
instance typDecidableLE (c : DeBruijn.Index) : DecidableLE (AST.Typ c)
  | .TLit, .TLit => isTrue rfl
  | .TLit, .TFn _ _
  | .TFn _ _, .TLit => isFalse (λ equality => nomatch equality)
  | .TFn leftIn leftOut, .TFn rightIn rightOut =>
    match typDecidableLE c leftIn rightIn, typDecidableLE c leftOut rightOut with
    | isTrue inputEqual, isTrue outputEqual => isTrue (inputEqual ▸ outputEqual ▸ rfl)
    | isFalse notEqual, _ => isFalse (λ equality => notEqual (by cases equality; rfl))
    | _, isFalse notEqual => isFalse (λ equality => notEqual (by cases equality; rfl))

namespace Val

def asTrm (self : AST.Val c) : AST.Trm c := .val self

end Val

end AST

end Lp2lc.Active.STLC
