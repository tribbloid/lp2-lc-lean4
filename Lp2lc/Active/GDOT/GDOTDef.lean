import «Lp2lc».Active.Parameters

/-!
Syntax based on [gDOT v1.0](https://github.com/Blaisorblade/dot-iris/blob/v1.0/theories/Dot/syn/syn.v).
As in STLC, `Parameters` chooses bytecode and lexical references; `Binder` extends the context.
Here `TLit` groups all bytecode values, and unary native `primitive` values replace the concrete
Int/Bool operations. Returning function values supports currying. Conditionals use a bytecode
predicate to select between `.fn` thunks, then apply only the chosen thunk.
Type definitions contain source syntax. Guarded reference constructs are commented out below
until their typing rules are settled. These are syntax declarations, independent of a proof framework.
-/

namespace Lp2lc.Active.GDOT

open Lp2lc.Active.Util

inductive Label where
| typ
| trm
| val
| path
| member
| members

namespace Pre

mutual

/-- A single lexical binder, including object self and dependent type binders. -/
inductive Binder : Parameters → Label → Type 2 where
| private body {P} (body : P.Next.TRef → AST P.Next l) : Binder P l

/-- Raw gDOT syntax; member names are strings, distinct from family tags. -/
inductive AST : Parameters → Label → Type 2 where

| TTop {P} : AST P .typ -- Any
| TBot {P} : AST P .typ -- Nothing
| TAnd {P} (left right : AST P .typ) : AST P .typ -- &, With
| TOr {P} (left right : AST P .typ) : AST P .typ -- |

| TLit {P} : AST P .typ -- primitive bytecode
| lit {P} (repr : P.B) : AST P .val

| TFn {P} (tIn : AST P .typ) (tOut : Binder P .typ) : AST P .typ -- ∀ x : S. T
| fn {P} (body : Binder P .trm) : AST P .val
-- A unary primitive may return another function value, so application supports currying.
| fnPrimitive {P} (op : P.B → AST P .val) : AST P .val

| ref {P} {P' : Parameters} (carrier : P'.TRef) (under : P'.Under P) : AST P .val

| pathDef {P} (path : AST P .path) : AST P .member
| typeDef {P} (typ : AST P .typ) : AST P .member -- ordinary source type definition
-- Named object definitions; this is the body of `obj`.
| nil {P} : AST P .members
| cons {P} (name : String) (member : AST P .member) (rest : AST P .members) : AST P .members

| TRec {P} (body : Binder P .typ) : AST P .typ -- μ x. T

| TField {P} (name : String) (typ : AST P .typ) : AST P .typ
| TMember {P} (name : String) (lower upper : AST P .typ) : AST P .typ
-- TODO: both type member and term fields are named, why is an object type be constructed by intersecting (TAnd) TField/TMember without order, but obj term must be constructed from members with order?
| obj {P} (body : Binder P .members) : AST P .val -- ν self. { ... }

-- TODO: .path already carries a name suffix for selection, why do we need name here again? Should it fold into TSingleton?
| TSel {P} (path : AST P .path) (name : String) : AST P .typ
| TSingleton {P} (path : AST P .path) : AST P .typ
| pathVal {P} (value : AST P .val) : AST P .path
| pathSel {P} (base : AST P .path) (name : String) : AST P .path

-- Reference forms are disabled until their typing rules are settled.
-- Guards recursive type-member reasoning in gDOT, even for immutable objects.
-- Interpreter fuel bounds a run; it does not remove this guard from the original typing rules.
-- | TLater {P} (typ : AST P .typ) : AST P .typ -- ▷ T
-- gDOT's `coerce`: e : ▷ T gives skip e : T, paying one extra reduction step.
-- | skip {P} (term : AST P .trm) : AST P .trm

| val {P} (value : AST P .val) : AST P .trm
| apply {P} (fn arg : AST P .trm) : AST P .trm
| proj {P} (base : AST P .trm) (name : String) : AST P .trm


end

namespace Binder

def mk := @body

end Binder

end Pre

end Lp2lc.Active.GDOT
