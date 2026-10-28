import «Lp2lc».Active.DTLC.Serial.Infra

namespace Lp2lc.Active.DTLC

open Lp2lc.Active.Util

namespace AST

variable {n m : Nat}

@[match_pattern] private abbrev bind := @Pre.Binder.mk

/-- Reindex type syntax structurally, opening binders through the supplied proxies.

The label is generalized to expose structural recursion on the indexed AST. Callers supply
only types and serial proxies; context reindexing does not consume inference fuel.
-/
private def resolveType {P l} (self : Pre.AST P l) (get : ∀ index, P.I.getTRef index)
    (target : Nat := 0) : Typ target :=
  match self with
  | .TFn input (bind output) =>
    .TFn (resolveType input get target)
      (.mk (λ _ => resolveType (output (get P.Next.index)) get (target + 1)))
  | _ => .TLit

private def typeMatches {P l m} (self : Pre.AST P l) (other : Typ m)
    (get : ∀ index, P.I.getTRef index) : Bool :=
  match self, other with
  | .TLit, .TLit => true
  | .TFn input (bind output), .TFn otherInput otherOutput =>
    typeMatches input otherInput get &&
      typeMatches (output (get P.Next.index)) (otherOutput.apply .only) get
  | _, _ => false

/-- Structural type equality, comparing output binders at their sole serial proxies. -/
def sameType {n m} (self : Typ n) (other : Typ m) : Rec Bool := λ fuel =>
  match fuel with
  | 0 => .outOfFuel
  | _ + 1 => .yield (typeMatches self other (λ _ => .only))

private def functionType (input : Typ n) (output : Typ m) : Typ :=
  .TFn (resolveType input (λ _ => .only)) (.mk (λ _ => resolveType output (λ _ => .only) 1))

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
        (infer (body.apply .only) (bindings.set (n + 1) ⟨n, input, .empty⟩) fuel).map
          (Option.map (functionType input))
      | .fnPrimitive output _ =>
        .yield (some (functionType (.TLit : Typ n) (output.apply .only)))
    | .ref _ under =>
      match bindings under.sourceIndex.down with
      | some (.inl ⟨_, typ, _⟩) => .yield (some (resolveType typ (λ _ => .only)))
      | some (.inr ⟨_, value, captured⟩) => infer value.asTrm captured fuel
      | none => .yield none
    | .apply fn arg =>
      match infer fn bindings fuel, infer arg bindings fuel with
      | .yield (some (.TFn input output)), .yield (some argType) =>
        (argType.sameType input fuel).flatMap (λ accepted =>
          if accepted then .yield (some (resolveType (output.apply .only) (λ _ => .only)))
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
