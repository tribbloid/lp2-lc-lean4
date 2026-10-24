import «Lp2lc».Active.DSub.Serial.Def

namespace Lp2lc.Active.DSub

open Lp2lc.Active.Util

/-- A source type with its lexical context and captured type bindings. -/
abbrev CompilerTyp := Closure (Typ ·)

/-- Runtime imports seed inference; subsequent bindings contain hypothetical types. -/
structure CompilerBindings where
  runtime : ExeBindings
  types : NatBindings CompilerTyp

namespace CompilerBindings

def breakpoint (bindings : ExeBindings) : CompilerBindings := ⟨bindings, .empty⟩

def empty : CompilerBindings := .breakpoint .empty

variable (self : CompilerBindings)

def set (index : Nat) (typ : CompilerTyp) : CompilerBindings :=
  { self with types := self.types.set index typ }

def get (index : Nat) : Option (CompilerTyp ⊕ ExeVal) :=
  ((self.types index).map .inl).orElse (λ _ => (self.runtime index).map .inr)

instance : CoeFun CompilerBindings (λ _ => Nat → Option (CompilerTyp ⊕ ExeVal)) := ⟨get⟩

instance : Coe ExeBindings CompilerBindings := ⟨breakpoint⟩

end CompilerBindings

end DSub
