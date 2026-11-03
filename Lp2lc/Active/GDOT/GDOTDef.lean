import «Lp2lc».Active.Parameters

/-!
Syntax based on [gDOT v1.0](https://github.com/Blaisorblade/dot-iris/blob/v1.0/theories/Dot/syn/syn.v).
Common cases follow [DSubDef.lean](../DSub/DSubDef.lean) in style and order.
`Parameters` supplies bytecode and lexical references; paths use the pure-expression family.
Here `TLit` groups all bytecode values, and unary native `fnPrimitive` values replace the concrete
Int/Bool operations. Returning function values supports currying. Conditionals use a bytecode
predicate to select between `.fn` thunks, then apply only the chosen thunk.
Type definitions contain source syntax. Guarded reference constructs are commented out below
until their typing rules are settled. These are syntax declarations, independent of a proof framework.
-/

namespace Lp2lc.Active.GDOT

open Lp2lc.Active.Util

inductive Label where
| typ
| val
| pure
| trm
| member
| members

namespace Pre

mutual

/-- A single lexical binder, including object self and dependent type binders. -/
inductive Binder : Parameters → Label → UAST where
| private body {P} (body : P.Next.TRef → AST P.Next l) : Binder P l

/-- Raw gDOT syntax; member names are strings, distinct from family tags. -/
inductive AST : Parameters → Label → UAST where
| TTop {P} : AST P .typ -- Any
| TBot {P} : AST P .typ -- Nothing
| TAnd {P} (left right : AST P .typ) : AST P .typ -- &, With
| TOr {P} (left right : AST P .typ) : AST P .typ -- |

| TLit {P} : AST P .typ -- primitive bytecode
| lit {P} (repr : P.B) : AST P .val

| TFn {P} (tIn : AST P .typ) (tOut : Binder P .typ) : AST P .typ -- ∀ x : S. T
| fn {P} (tIn : AST P .typ) (body : Binder P .trm) : AST P .val
-- A unary primitive may return another function value, so application supports currying.
| fnPrimitive {P} (tOut : Binder P .typ) (op : P.B → AST P .val) : AST P .val

-- Recursive types bind self; singleton types select the type inhabited by one path.
| TRec {P} (body : Binder P .typ) : AST P .typ -- μ x. T

| TField {P} (name : String) (typ : AST P .typ) : AST P .typ
/-- `{ type A >: L <: U }` -/
| TMember {P} (name : String) (lower upper : AST P .typ) : AST P .typ
/-- `value.A`, selecting a named type member of a stable pure expression. -/
| TSel {P} (value : AST P .pure) (name : String) : AST P .typ
/-- `type A = T`, with the name supplied by the enclosing `cons`. -/
| typeDef {P} (typ : AST P .typ) : AST P .member

| TSingleton {P} (value : AST P .pure) : AST P .typ -- xx.type
| pathDef {P} (path : AST P .pure) : AST P .member
-- Named object definitions; this is the body of `obj`.
| nil {P} : AST P .members
| cons {P} (name : String) (member : AST P .member) (rest : AST P .members) : AST P .members
-- TODO: clarify why object types use TAnd over named TField/TMember declarations,
-- while obj bodies use ordered named definitions; distinguish syntax from typing equivalence.
| obj {P} (body : Binder P .members) : AST P .val -- ν self. { ... }

| val {P} (this : AST P .val) : AST P .pure

/-- Lexical references are pure expressions and may occur in type selections. -/
| ref {P} {P' : Parameters} (carrier : P'.TRef) (under : P'.Under P) : AST P .pure

| pathSel {P} (base : AST P .pure) (name : String) : AST P .pure

-- Reference forms are disabled until their typing rules are settled.
-- Guards recursive type-member reasoning in gDOT, even for immutable objects.
-- Interpreter fuel bounds a run; it does not remove this guard from the original typing rules.
-- | TLater {P} (typ : AST P .typ) : AST P .typ -- ▷ T
-- gDOT's `coerce`: e : ▷ T gives skip e : T, paying one extra reduction step.
-- | skip {P} (term : AST P .trm) : AST P .trm

| pure {P} (this : AST P .pure) : AST P .trm
| apply {P} (fn arg : AST P .trm) : AST P .trm
| proj {P} (base : AST P .trm) (name : String) : AST P .trm

end

namespace Binder

def mk := @body

/-- Open a binder under the index encoding's reference contract. -/
def apply {P l} (self : Binder P l) (carrier) :=
  match self with
  | .body code => code carrier

end Binder

end Pre

end Lp2lc.Active.GDOT
