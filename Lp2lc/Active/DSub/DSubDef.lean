import «Lp2lc».Active.Parameters

/-!
Syntax adapted from [DSub](https://github.com/Blaisorblade/dot-iris/blob/master/theories/DSub/syn/syn.v).
As in GDOT, `Parameters` supplies bytecode and lexical references; `TLit` generalizes integers.
Source `typeDef` values replace semantic stamps. The sole type member needs no name or separate path.
-/

namespace Lp2lc.Active.DSub

open Lp2lc.Active.Util

inductive Label where
| typ
| trm
| val

namespace Pre

mutual

/-- A single lexical binder for functions and dependent result types. -/
inductive Binder : Parameters → Label → Type 2 where
| private body {P} (body : P.Next.TRef → AST P.Next l) : Binder P l

inductive AST : Parameters → Label → Type 2 where
| TTop {P} : AST P .typ
| TBot {P} : AST P .typ

| TLit {P} : AST P .typ
| lit {P} (repr : P.B) : AST P .val

| TFn {P} (tIn : AST P .typ) (tOut : Binder P .typ) : AST P .typ -- ∀ x : S. T
| fn {P} (tIn : AST P .typ) (body : Binder P .trm) : AST P .val -- dependent function
| fnPrimitive {P} (tOut : Binder P .typ) (op : P.B → AST P .val) : AST P .val
    -- inference uses declared `.TFn .TLit tOut`; evaluation must validate each result of `op`

| TMember {P} (lower upper : AST P .typ) : AST P .typ -- Scala type: { type Type >: L <: U }
| TSel {P} (value : AST P .val) : AST P .typ -- Scala type: v.Type (stable v)
| typeDef {P} (typ : AST P .typ) : AST P .val -- Scala value: new { type Type = T }

| ref {P} {P' : Parameters} (carrier : P'.TRef) (under : P'.Under P) : AST P .val

-- Upstream guarded forms are deferred, as in GDOT, until their typing rules are settled.
-- | TLater {P} (typ : AST P .typ) : AST P .typ -- ▷ T
-- | skip {P} (term : AST P .trm) : AST P .trm

| val {P} (value : AST P .val) : AST P .trm
| apply {P} (fn arg : AST P .trm) : AST P .trm

end

namespace Binder

def mk := @body

/-- Open a binder under the index encoding's reference contract. -/
def apply {P l} (self : Binder P l) (carrier) :=
  match self with
  | .body code => code carrier

end Binder

end Pre

end Lp2lc.Active.DSub
