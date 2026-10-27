import «Lp2lc».Active.DTLC.Serial.Infra

namespace Lp2lc.Active.DTLC

open Lp2lc.Active.Util

namespace AST

variable {n m : Nat}

/-- Reindex types, opening output binders only at the serial proxy.

The current type syntax contains only `TLit` and `TFn`, so it has no references to substitute
or captured bindings to resolve. Fuel also bounds traversal beneath output binders.
-/
private def resolveType {n} (self : Typ n) (target : Nat := 0) : Rec (Typ target) := λ fuel =>
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .TLit => .yield .TLit
    | .TFn input output =>
      (AST.resolveType input target fuel).flatMap (λ input =>
        (AST.resolveType (output.apply .only) (target + 1) fuel).map (λ output =>
          .TFn input (.mk (λ _ => output))))

/-- Structural type equality, comparing output binders at their sole serial proxies. -/
def sameType {n m} (self : Typ n) (other : Typ m) : Rec Bool := λ fuel =>
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self, other with
    | .TLit, .TLit => .yield true
    | .TFn input output, .TFn otherInput otherOutput =>
      (sameType input otherInput fuel).flatMap (λ same =>
        if same then sameType (output.apply .only) (otherOutput.apply .only) fuel
        else .yield false)
    | _, _ => .yield false

private def functionType (input : Typ n) (output : Typ m) : Rec Typ := λ fuel =>
  (input.resolveType 0 fuel).flatMap (λ input =>
    (output.resolveType 1 fuel).map (λ output => .TFn input (.mk (λ _ => output))))

/-- Infer from runtime values and hypothetical parameter types, returning a context-zero type.
Primitive annotations determine their inferred types; evaluation checks their implementations.
-/
def infer {n} (self : Trm n) (bindings : CompilerBindings := .empty) : RecOpt Typ := λ fuel =>
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value =>
      match value with
      | .lit _ => .yield (some .TLit)
      | .fn input body =>
        (infer (body.apply .only) (bindings.set (n + 1) ⟨n, input, .empty⟩) fuel).flatMap (λ output =>
          match output with
          | some output => (functionType input output fuel).map some
          | none => .yield none)
      | .fnPrimitive output _ =>
        (functionType (.TLit : Typ n) (output.apply .only) fuel).map some
    | .ref _ under =>
      match bindings under.sourceIndex.down with
      | some (.inl ⟨_, typ, _⟩) => (typ.resolveType 0 fuel).map some
      | some (.inr ⟨_, value, captured⟩) => infer value.asTrm captured fuel
      | none => .yield none
    | .apply fn arg =>
      match infer fn bindings fuel, infer arg bindings fuel with
      | .yield (some (.TFn input output)), .yield (some argType) =>
        (argType.sameType input fuel).flatMap (λ accepted =>
          if accepted then (resolveType (output.apply .only) 0 fuel).map some
          else .yield none)
      | .yield _, .yield _ => .yield none
      | _, _ => .outOfFuel

def semType (self : Trm n) (bindings : CompilerBindings) (fuel : Nat) (typ : Typ) : Prop :=
  self.infer bindings fuel = .yield (some typ)

namespace Monotone

/-- Conjecture: every completed inference result is preserved when fuel increases. -/
theorem termInfer (trm : Trm n) (bindings : CompilerBindings) :
    (infer trm bindings).Monotone := by
  sorry

end Monotone

end AST

end Lp2lc.Active.DTLC
