import «Lp2lc».Active.Parameters

/-!
Higher-kinded syntax from [HK-gDOT #302](https://github.com/Blaisorblade/dot-iris/pull/302), linked by #360.
The bytecode, curried primitive, thunked conditional, guarded and stamped conventions are shared
with [GDOTDef.lean](../GDOT/GDOTDef.lean). This extension adds type lambdas, path application,
kind-valued type members, interval kinds, and value-dependent function kinds.
-/

namespace Lp2lc.Active.HKGDOT

open Lp2lc.Active.Util

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
| lit {P} (repr : P.B) : AST P .val

| TFn {P} (tIn : AST P .typ) (tOut : Binder P .typ) : AST P .typ
| fn {P} (body : Binder P .trm) : AST P .val
-- A unary primitive may return another function value, so application supports currying.
| primitive {P} (op : P.B → AST P .val) : AST P .val
| apply {P} (fn arg : AST P .trm) : AST P .trm

| TLam {P} (body : Binder P .typ) : AST P .typ -- λ x. T
| TApply {P} (fn : AST P .typ) (arg : AST P .path) : AST P .typ -- T p
| KPi {P} (tIn : AST P .typ) (body : Binder P .kind) : AST P .kind -- Π x : S. K

| TRec {P} (body : Binder P .typ) : AST P .typ
| obj {P} (body : Binder P .members) : AST P .val

| TField {P} (name : String) (typ : AST P .typ) : AST P .typ
| pathDef {P} (path : AST P .path) : AST P .member
| proj {P} (base : AST P .trm) (name : String) : AST P .trm

| TMember {P} (name : String) (kind : AST P .kind) : AST P .typ
| KInterval {P} (lower upper : AST P .typ) : AST P .kind -- L .. U
| typeDef {P} (typ : AST P .typ) : AST P .member
-- Auxiliary semantic-type identity and its captured value substitution, as in gDOT.
| typeStamp {P} (env : AST P .values) (stamp : Nat) : AST P .member

| TSel {P} (arity : Nat) (path : AST P .path) (name : String) : AST P .typ -- 0 for gDOT
| TSingleton {P} (path : AST P .path) : AST P .typ
| pathVal {P} (value : AST P .val) : AST P .path
| pathSel {P} (base : AST P .path) (name : String) : AST P .path

| TTop {P} : AST P .typ
| TBot {P} : AST P .typ
| TAnd {P} (left right : AST P .typ) : AST P .typ
| TOr {P} (left right : AST P .typ) : AST P .typ
-- The original guard for recursive type-member reasoning is independent of interpreter fuel.
| TLater {P} (typ : AST P .typ) : AST P .typ
-- Eliminates one `TLater` after an extra reduction step, as in gDOT.
| skip {P} (term : AST P .trm) : AST P .trm

| ref {P} {P' : Parameters} (carrier : P'.TRef) (under : P'.Under P) : AST P .val
| val {P} (value : AST P .val) : AST P .trm

-- Named object definitions, followed by the unnamed values captured by `typeStamp`.
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
