import «Lp2lc».Active.DTLC.Serial.Def

namespace Lp2lc.Active.DTLC

open Lp2lc.Active.Util

/-- A source type together with its lexical context and captured type bindings. -/
abbrev CompilerTyp := Closure (Typ ·)

/-- Runtime values seed inference; lambda parameters introduce hypothetical types. -/
structure CompilerBindings where
  runtime : ExeBindings
  types : NatBindings CompilerTyp

namespace CompilerBindings

abbrev breakpoint (bindings : ExeBindings) : CompilerBindings := ⟨bindings, .empty⟩

def empty : CompilerBindings := breakpoint .empty

variable (self : CompilerBindings)

abbrev set (index : Nat) (typ : CompilerTyp) : CompilerBindings :=
  { self with types := self.types.set index typ }

def get (index : Nat) : Option (CompilerTyp ⊕ ExeVal) :=
  ((self.types index).map .inl).orElse (λ _ => (self.runtime index).map .inr)

instance : CoeFun CompilerBindings (λ _ => Nat → Option (CompilerTyp ⊕ ExeVal)) := ⟨get⟩

instance : Coe ExeBindings CompilerBindings := ⟨breakpoint⟩

end CompilerBindings

/-- Reindex types, opening output binders only at the serial proxy.

The current type syntax contains only `TLit` and `TFn`, so it has no references to substitute
or captured bindings to resolve. Fuel also bounds traversal beneath output binders.
-/
def AST.resolveType {n} (self : Typ n) (target : Nat := 0) : Rec (Typ target) := λ fuel =>
  match fuel, self with
  | 0, _ => .outOfFuel
  | _ + 1, .TLit => .yield .TLit
  | fuel + 1, .TFn input output =>
    (AST.resolveType input target fuel).flatMap (λ input =>
      (AST.resolveType (output.apply .only) (target + 1) fuel).map (λ output =>
        .TFn input (.mk (λ _ => output))))

end DTLC
