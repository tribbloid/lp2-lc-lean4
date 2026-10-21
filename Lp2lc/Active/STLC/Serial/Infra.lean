import «Lp2lc».Active.STLC.Serial.Def

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

/-- A value or type together with its lexical context and captured compiler bindings. -/
structure CompilerTyp : Type 2 where
  n : Nat
  either : Typ n -- CompilerTyp can bind other type but not value (singleton type is still a type)
  captured : NatBindings CompilerTyp

abbrev CompilerBindings := NatBindings (CompilerTyp ⊕ ExeVal) -- append-only

def ExeValue.toCompiler (self : ExeVal) : CompilerTyp :=
  match self with
  | ⟨n, value, captured⟩ =>
    ⟨n, .inl value, ⟨captured.entries.map (λ entry => (entry.1, entry.2.toCompiler))⟩⟩
decreasing_by
  cases ‹Nat × ExeVal›
  have := List.sizeOf_lt_of_mem (by assumption)
  cases captured
  simp_all
  omega

/-- Erase an STLC type's context index without consuming inference or checking fuel. -/
def AST.resolveType {n} (self : Typ n) : Typ :=
  match self with
  | .TLit => .TLit
  | .TFn input output => .TFn (AST.resolveType input) (AST.resolveType output)

end STLC
