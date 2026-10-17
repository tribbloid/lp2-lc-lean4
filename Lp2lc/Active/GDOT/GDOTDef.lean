import «Lp2lc».Active.Parameters

/-!
Syntax based on [gDOT v1.0](https://github.com/Blaisorblade/dot-iris/blob/v1.0/theories/Dot/syn/syn.v).
As in STLC, `Parameters` chooses bytecode and lexical references; `Binder` extends the context.
Here `TLit` groups all bytecode values, and unary native `primitive` values replace the concrete
Int/Bool operations. Returning function values supports currying. Conditionals use a bytecode
predicate to select between `.fn` thunks, then apply only the chosen thunk.
The guarded constructs and source/stamped type definitions retain the reference grammar's forms;
their roles are explained below. These are syntax declarations, independent of a proof framework.
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
| values

namespace Pre

mutual

/-- A single lexical binder, including object self and dependent type binders. -/
inductive Binder : Parameters → Label → Type 2 where
| private body {P} (body : P.Next.TRef → AST P.Next l) : Binder P l

/-- Raw gDOT syntax; member names are strings, distinct from family tags. -/
inductive AST : Parameters → Label → Type 2 where
| TLit {P} : AST P .typ -- primitive bytecode
| lit {P} (repr : P.B) : AST P .val

| TFn {P} (tIn : AST P .typ) (tOut : Binder P .typ) : AST P .typ -- ∀ x : S. T
| fn {P} (body : Binder P .trm) : AST P .val
-- A unary primitive may return another function value, so application supports currying.
| primitive {P} (op : P.B → AST P .val) : AST P .val
| apply {P} (fn arg : AST P .trm) : AST P .trm

| TRec {P} (body : Binder P .typ) : AST P .typ -- μ x. T
| obj {P} (body : Binder P .members) : AST P .val -- ν self. { ... }

| TField {P} (name : String) (typ : AST P .typ) : AST P .typ
| pathDef {P} (path : AST P .path) : AST P .member
| proj {P} (base : AST P .trm) (name : String) : AST P .trm

| TMember {P} (name : String) (lower upper : AST P .typ) : AST P .typ
| typeDef {P} (typ : AST P .typ) : AST P .member -- ordinary source type definition
-- TODO: semantically stamped AST permits defining exotic type, this is bad, should be replaced by
-- Auxiliary stamped form used by the reference soundness model: `stamp` names a semantic type,
-- and `env` is its finite value substitution. Ordinary source syntax uses `typeDef` instead.
| typeStamp {P} (env : AST P .values) (stamp : Nat) : AST P .member

| TSel {P} (path : AST P .path) (name : String) : AST P .typ
| TSingleton {P} (path : AST P .path) : AST P .typ
| pathVal {P} (value : AST P .val) : AST P .path
| pathSel {P} (base : AST P .path) (name : String) : AST P .path

| TTop {P} : AST P .typ
| TBot {P} : AST P .typ
| TAnd {P} (left right : AST P .typ) : AST P .typ
| TOr {P} (left right : AST P .typ) : AST P .typ

-- TODO: for the moment these should be commented oout as we are not certain of typing rule yet.
-- Guards recursive type-member reasoning in gDOT, even for immutable objects.
-- Interpreter fuel bounds a run; it does not remove this guard from the original typing rules.
| TLater {P} (typ : AST P .typ) : AST P .typ -- ▷ T
-- gDOT's `coerce`: e : ▷ T gives skip e : T, paying one extra reduction step.
| skip {P} (term : AST P .trm) : AST P .trm

| ref {P} {P' : Parameters} (carrier : P'.TRef) (under : P'.Under P) : AST P .val
| val {P} (value : AST P .val) : AST P .trm

-- Named object definitions; this is the body of `obj`.
| nil {P} : AST P .members
| cons {P} (name : String) (member : AST P .member) (rest : AST P .members) : AST P .members

-- Unnamed captured values for `typeStamp`; their element type differs from object definitions.
| nilValues {P} : AST P .values
| consValues {P} (value : AST P .val) (rest : AST P .values) : AST P .values

end

namespace Binder

def mk := @body

end Binder

end Pre

end Lp2lc.Active.GDOT
