import «Lp2lc».Active.Parameters

namespace Lp2lc.Active.GDOT

open Lp2lc.Active.Util

-- Original gDOT: https://github.com/Blaisorblade/dot-iris/blob/v1.0/theories/Dot/syn/syn.v
inductive Prim where
| int
| bool

inductive Literal where
| int (value : Int)
| bool (value : Bool)

inductive BinOp where
| add
| sub
| mul
| div
| lt
| le
| eq

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
| TLit {P} (prim : Prim) : AST P .typ
| TTop {P} : AST P .typ
| TBot {P} : AST P .typ
| TAnd {P} (left right : AST P .typ) : AST P .typ
| TOr {P} (left right : AST P .typ) : AST P .typ
| TLater {P} (typ : AST P .typ) : AST P .typ -- ▷ T
| TFn {P} (tIn : AST P .typ) (tOut : Binder P .typ) : AST P .typ -- ∀ x : S. T
| TRec {P} (body : Binder P .typ) : AST P .typ -- μ x. T
| TField {P} (name : String) (typ : AST P .typ) : AST P .typ
| TMember {P} (name : String) (lower upper : AST P .typ) : AST P .typ
| TSel {P} (path : AST P .path) (name : String) : AST P .typ
| TSingleton {P} (path : AST P .path) : AST P .typ

| lit {P} (repr : Literal) : AST P .val
| fn {P} (body : Binder P .trm) : AST P .val
| obj {P} (body : Binder P .members) : AST P .val -- ν self. { ... }
| ref {P} {P' : Parameters} (carrier : P'.TRef) (under : P'.Under P) : AST P .val

| val {P} (value : AST P .val) : AST P .trm
| apply {P} (fn arg : AST P .trm) : AST P .trm
| proj {P} (base : AST P .trm) (name : String) : AST P .trm
| skip {P} (term : AST P .trm) : AST P .trm -- coerce e
| not {P} (term : AST P .trm) : AST P .trm
| binary {P} (op : BinOp) (left right : AST P .trm) : AST P .trm
| cond {P} (test yes no : AST P .trm) : AST P .trm

| pathVal {P} (value : AST P .val) : AST P .path
| pathSel {P} (base : AST P .path) (name : String) : AST P .path
| typeDef {P} (typ : AST P .typ) : AST P .member
| typeStamp {P} (env : AST P .values) (stamp : Nat) : AST P .member
| pathDef {P} (path : AST P .path) : AST P .member
| nil {P} : AST P .members
| cons {P} (name : String) (member : AST P .member) (rest : AST P .members) : AST P .members
| nilValues {P} : AST P .values
| consValues {P} (value : AST P .val) (rest : AST P .values) : AST P .values

end

namespace Binder

def mk := @body

end Binder

end Pre

end Lp2lc.Active.GDOT
