import «Lp2lc».Active.Util
import «Lp2lc».Active.Parameters

namespace Lp2lc.Active.STLC_minimal

open Lp2lc.Active.Util

/-
Unreified AST with parametric carrier

Rule: this is an internal API, actual language should use AST/Binder under STLC namespace
-/
namespace Pre

mutual

/-- A binder introduces the next lexical context for its body. -/
inductive Binder : Parameters → Label → UAST where
    /-- Internal construction callback; do not consume it as a nonuniform function.

    Use `Binder.apply` under the index encoding's opening contract. UId opens only at `.inr ()`
    and substitutes receipts structurally; serial binders receive their sole context proxy.
    -/
| private body {P} (body : P.Next.TRef → AST P.Next l) : Binder P l

/-- Source type, value, and term syntax.

`TLit` classifies primitive bytecode values and `TFn` classifies functions.
-/
inductive AST : Parameters → Label → UAST where
| TLit {P} : AST P .typ -- `AnyVal` in Scala, accepts only primitive values
| lit {P} (repr : P.B) : AST P .val -- most specific type is always `.TLit`

| TFn {P} (tIn : AST P .typ) (tOut : AST P .typ) : AST P .typ -- function
| fn {P} (tIn : AST P .typ) (body : Binder P .trm) : AST P .val
    -- most specific type is always `.TFn tIn _`
| fnPrimitive {P} (tOut : AST P .typ) (op : P.B → AST P .val) : AST P .val

| val {P} (v : AST P .val) : AST P .trm -- AKA literal
| apply {P} (fn : AST P .trm) (arg : AST P .trm) : AST P .trm
    -- fn must be a function that can be applied on arg
-- A lexical reference retains its source context and a witness reaching the current context.
| ref {P} {P' : Parameters} (carrier : P'.TRef)
    (under : P'.Under P) : AST P .trm
 end

namespace Binder
-- All theorems about Binder should be here, e.g. parametricity, lift relation

/-- Constructs a binder whose body is consumed under its index encoding's opening contract. -/
def mk := @body

/-- Opens a binder body with the supplied reference receipt. -/
def apply {P l} (self : Binder P l) (carrier) := match self with
  | .body code => code carrier

end Binder

end Pre

end Lp2lc.Active.STLC_minimal
