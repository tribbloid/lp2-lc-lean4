import «Lp2lc».Active.STLC.Serial.Eval

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

/-- Executable, sound search for a supplied type; no principal type is computed.
`inputs` supplies finite application witnesses, each checked against both operands.
`false` means this search failed, not that the full semantic specification is false.
-/
def checkInternal {n} (self : Trm n) (typ : Typ)
    (bindings : CompilerBindings := .empty) : Rec Prop := λ fuel =>
  match fuel with
  | 0 => .yield False
  | fuel + 1 => sorry

def check {n} (self : Trm n) (typ : Typ)
    (bindings : ExeBindings := .empty) : Rec Prop :=
  self.checkInternal (exeBindings.map .inl)

def semType {n} (self : Trm n) (bindings : CompilerBindings) (fuel : Nat) (typ: Typ) : Prop :=
  self.checkInternal typ bindings fuel

end Lp2lc.Active.STLC.AST.Semantic
