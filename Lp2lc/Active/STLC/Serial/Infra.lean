import «Lp2lc».Active.STLC.Serial.Def

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

/-- A type together with its lexical context and captured type bindings. -/
abbrev CompilerTyp := Closure (Typ ·) -- Compiler types capture only other types; singleton types remain types.

/-- Breakpoint values seed inference; subsequent bindings must contain only hypothetical types. -/
inductive CompilerBindings where
  | breakpoint (bindings : ExeBindings)
  | set (self : CompilerBindings) (index : Nat) (typ : CompilerTyp)

namespace CompilerBindings

def empty : CompilerBindings := breakpoint .empty

def get (self : CompilerBindings) (index : Nat) : Option (CompilerTyp ⊕ ExeVal) :=
  match self with
  | .breakpoint bindings => (bindings index).map .inr
  | .set bindings key typ => if key = index then some (.inl typ) else bindings.get index

instance : CoeFun CompilerBindings (λ _ => Nat → Option (CompilerTyp ⊕ ExeVal)) := ⟨get⟩

instance : Coe ExeBindings CompilerBindings := ⟨breakpoint⟩

end CompilerBindings

/-- Erase an STLC type's context index without consuming inference or checking fuel. -/
def AST.resolveType {n} (self : Typ n) : Typ :=
  match self with
  | .TLit => .TLit
  | .TFn input output => .TFn (AST.resolveType input) (AST.resolveType output)

end STLC
