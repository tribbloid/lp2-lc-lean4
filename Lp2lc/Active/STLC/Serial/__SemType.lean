import «Lp2lc».Active.STLC.Serial.Eval
import «Lp2lc».Active.STLC.Serial.Infra

namespace Lp2lc.Active.STLC.AST.Semantic

open Lp2lc.Active.Util

/-- Fuel-bounded expected-type checking with runtime values or hypothetical types. -/
def checkInternal {n} (self : Trm n) (typ : Typ)
    (bindings : CompilerBindings := .empty) : Rec Prop := λ fuel =>
  match fuel with
  | 0 => .yield False
  | fuel + 1 => sorry

def check {n} (self : Trm n) (typ : Typ)
    (bindings : ExeBindings := .empty) : Rec Prop :=
  checkInternal self typ (bindings.map .inl)

def semType {n} (self : Trm n) (bindings : CompilerBindings) (fuel : Nat) (typ: Typ) : Prop :=
  (checkInternal self typ bindings fuel).getOrElse False

end Lp2lc.Active.STLC.AST.Semantic
