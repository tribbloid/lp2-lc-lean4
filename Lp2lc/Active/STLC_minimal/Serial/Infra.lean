import «Lp2lc».Active.STLC_minimal.Serial.Def

namespace Lp2lc.Active.STLC_minimal

open Lp2lc.Active.Util

abbrev CompilerTyp := Closure (Typ ·)

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

def AST.resolveType {n} (self : Typ n) : Typ :=
  match self with
  | .TLit => .TLit
  | .TFn input output => .TFn (AST.resolveType input) (AST.resolveType output)

end STLC_minimal
