import «Lp2lc».Active.STLC.Serial.Eval
import «Lp2lc».Active.STLC.Serial.Infra

namespace Lp2lc.Active.STLC.AST.Semantic

open Lp2lc.Active.Util

/-- Fuel-bounded typing with runtime values or hypothetical types.

Application quantifies over its domain; no principal type is selected.
-/
def check {n} (self : Trm n) (typ : Typ)
    (bindings : CompilerBindings := .empty) : Rec Prop
  | 0 => .yield False
  | fuel + 1 =>
    .yield (match self, typ with
      | .pure (.val (.lit _)), .TLit => True
      | .pure (.val (.lit _)), .TFn _ _
      | .pure (.val (.fn _ _)), .TLit => False
      | .pure (.val (.fn annotation body)), .TFn input output =>
        resolveType annotation = input ∧
          (check (body.apply .only) output
            (bindings.set (n + 1) ⟨n, annotation, .empty⟩) fuel).getOrElse False
      | .pure (.ref _ under), _ =>
        match bindings under.sourceIndex.down with
        | some (.inl ⟨_, bound, _⟩) => resolveType bound = typ
        | some (.inr ⟨_, value, captured⟩) => (check value.asTrm typ captured fuel).getOrElse False
        | none => False
      | .apply fn arg, _ =>
        ∃ input, (check fn (.TFn input typ) bindings fuel).getOrElse False ∧
          (check arg input bindings fuel).getOrElse False
      | .pure (.val (.fnPrimitive tOut _)), _ => typ = .TFn .TLit (resolveType tOut))

def semType {n} (self : Trm n) (bindings : CompilerBindings) (fuel : Nat) (typ: Typ) : Prop :=
  (check self typ bindings fuel).getOrElse False

end Lp2lc.Active.STLC.AST.Semantic
