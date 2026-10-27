import «Lp2lc».Active.Util
import «Lp2lc».Active.Parameters

namespace Lp2lc.Active.STLC

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
/-- `AnyVal/Int/Bool/Double ...`, differentiating them is trivial and won't be included in this proof -/
| TLit {P} : AST P .typ
/-- `v: _Lit`, most specific type is always `.TLit` -/
| lit {P} (repr : P.B) : AST P .val

/-- `In => Out`, function type -/
| TFn {P} (tIn : AST P .typ) (tOut : AST P .typ) : AST P .typ
/-- `fn: _Fn with (In => ?)`. AKA lambda -/
| fn {P} (tIn : AST P .typ) (body : Binder P .trm) : AST P .val
/-- `fnPrimitive: _Fn with (_Lit => Out)`, unlike above, it can contain binary computation.
Technically not part of STLC. AKA PrimitiveOp -/
| fnPrimitive {P} (tOut : AST P .typ) (op : P.B → AST P .val) : AST P .val

/-- A lexical reference retains its source context and a witness reaching the current context. AKA variable, var -/
| ref {P} {P' : Parameters} (carrier : P'.TRef) (under : P'.Under P) : AST P .trm

/-- a thin wrapper of value as term -/
| val {P} (v : AST P .val) : AST P .trm -- AKA literal
/-- `fn (arg)`, `fn` and `arg` should be converted to ANF first -/
| apply {P} (fn : AST P .trm) (arg : AST P .trm) : AST P .trm

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

end Lp2lc.Active.STLC
