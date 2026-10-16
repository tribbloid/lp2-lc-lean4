import «Lp2lc».Active.Parameters

namespace Lp2lc.Active.HKGDOT

open Lp2lc.Active.Util

-- HK-gDOT syntax from https://github.com/Blaisorblade/dot-iris/pull/302 (linked by #360).
inductive Label where
| typ
| trm
| val
| path
| member
| members
| values
| kind

namespace Pre

mutual

/-- A single lexical binder; type constructors bind values, just like dependent functions. -/
inductive Binder : Parameters → Label → Type 2 where
| private body {P} (body : P.Next.TRef → AST P.Next l) : Binder P l

/-- Raw HK-gDOT syntax, with interval and dependent function kinds. -/
inductive AST : Parameters → Label → Type 2 where
| TLit {P} : AST P .typ -- primitive bytecode
| TTop {P} : AST P .typ
| TBot {P} : AST P .typ
| TAnd {P} (left right : AST P .typ) : AST P .typ
| TOr {P} (left right : AST P .typ) : AST P .typ
| TLater {P} (typ : AST P .typ) : AST P .typ
| TFn {P} (tIn : AST P .typ) (tOut : Binder P .typ) : AST P .typ
| TRec {P} (body : Binder P .typ) : AST P .typ
| TField {P} (name : String) (typ : AST P .typ) : AST P .typ
| TMember {P} (name : String) (kind : AST P .kind) : AST P .typ
| TSel {P} (arity : Nat) (path : AST P .path) (name : String) : AST P .typ -- 0 for gDOT
| TSingleton {P} (path : AST P .path) : AST P .typ
| TLam {P} (body : Binder P .typ) : AST P .typ -- λ x. T
| TApply {P} (fn : AST P .typ) (arg : AST P .path) : AST P .typ -- T p
| KInterval {P} (lower upper : AST P .typ) : AST P .kind -- L .. U
| KPi {P} (tIn : AST P .typ) (body : Binder P .kind) : AST P .kind -- Π x : S. K

| lit {P} (repr : P.B) : AST P .val
| fn {P} (body : Binder P .trm) : AST P .val
| obj {P} (body : Binder P .members) : AST P .val
| ref {P} {P' : Parameters} (carrier : P'.TRef) (under : P'.Under P) : AST P .val

| val {P} (value : AST P .val) : AST P .trm
| apply {P} (fn arg : AST P .trm) : AST P .trm
| proj {P} (base : AST P .trm) (name : String) : AST P .trm
| skip {P} (term : AST P .trm) : AST P .trm
| unary {P} (op : P.B → P.B) (term : AST P .trm) : AST P .trm
| binary {P} (op : P.B → P.B → P.B) (left right : AST P .trm) : AST P .trm
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

end Lp2lc.Active.HKGDOT
