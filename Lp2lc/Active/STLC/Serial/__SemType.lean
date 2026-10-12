import «Lp2lc».Active.STLC.Serial.Eval
import «Lp2lc».Active.STLC.Serial.Infra

namespace Lp2lc.Active.STLC.AST.Semantic

open Lp2lc.Active.Util

-- /-- A semantic function must safely handle every argument of its input type.
-- Annotations are hints: the evaluator ignores them, so this relation does too.
-- -/
-- def ValueHasType (typ : Typ) (value : ExeValue) : Prop :=
--   match typ, value with
--   | .TLit, .mk _ (.lit _) _ => True
--   | .TFn input output, .mk context (.fn _ body) captured =>
--     ∀ argument, ValueHasType input argument →
--       (eval (body.apply .only) (captured.set (context + 1) argument)).isSemiDecidable
--         (ValueHasType output)
--   | _, _ => False

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
