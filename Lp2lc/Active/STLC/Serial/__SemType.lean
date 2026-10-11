import «Lp2lc».Active.STLC.Serial.Eval

namespace Lp2lc.Active.STLC.AST.Semantic

open Lp2lc.Active.Util

/-- A semantic function must safely handle every argument of its input type.
Annotations are hints: the evaluator ignores them, so this relation does too.
-/
def ValueHasType (typ : Typ) (value : ExeValue) : Prop :=
  match typ, value with
  | .TLit, .mk _ (.lit _) _ => True
  | .TFn input output, .mk context (.fn _ body) captured =>
    ∀ argument, ValueHasType input argument →
      (eval (body.apply .only) (captured.set (context + 1) argument)).isSemiDecidable
        (ValueHasType output)
  | _, _ => False

/-- Every evaluation either needs more fuel or returns a value satisfying the logical relation.
This specifies safety without requiring termination or consulting the checker.
-/
def SemType {n} (trm : Trm n) (bindings : ExeBindings) (typ : Typ) : Prop :=
  (trm.eval bindings).isSemiDecidable (ValueHasType typ)

abbrev CheckBindings := NatBindings (ExeValue ⊕ Typ)

/-- Relates hypothetical input types and captured values to an actual execution environment. -/
def EnvFits (source : CheckBindings) (target : ExeBindings) : Prop :=
  ∀ index, match source index with
  | none => True
  | some (.inl value) => target index = some value
  | some (.inr typ) => ∃ value, target index = some value ∧ ValueHasType typ value

/-- Executable, sound search for a supplied type; no principal type is computed.
`inputs` supplies finite application witnesses, each checked against both operands.
`false` means this search failed, not that the full semantic specification is false.
-/
def check {n} (self : Trm n) (typ : Typ) (inputs : List Typ)
    (bindings : CheckBindings := .empty) : (fuel : Nat) → Bool := λ fuel =>
  match fuel with
  | 0 => false
  | fuel + 1 =>
    match self with
    | .val (.lit _) => decide (typ ≤ .TLit)
    | .val (.fn _ body) =>
      match typ with
      | .TLit => false
      | .TFn input output =>
        check (body.apply .only) output inputs (bindings.set (n + 1) (.inr input)) fuel
    | .ref _ under =>
      match bindings under.sourceIndex.down with
      | none => false
      | some (.inr input) => decide (input ≤ typ)
      | some (.inl (.mk _ value captured)) =>
        check value.asTrm typ inputs (captured.map .inl) fuel
    | .apply fn arg =>
      inputs.any (λ input =>
        check fn (.TFn input typ) inputs bindings fuel && check arg input inputs bindings fuel)

end Lp2lc.Active.STLC.AST.Semantic
