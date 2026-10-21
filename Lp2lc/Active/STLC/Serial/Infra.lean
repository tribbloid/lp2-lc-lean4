import «Lp2lc».Active.STLC.Serial.Def

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

/-- A type together with its lexical context and captured type bindings. -/
structure CompilerTyp : Type 2 where
  n : Nat
  either : Typ n -- Compiler types capture only other types; singleton types remain types.
  captured : NatBindings CompilerTyp

/-- Breakpoint values seed inference; subsequent bindings must contain only hypothetical types. -/
abbrev CompilerBindings := NatBindings (CompilerTyp ⊕ ExeVal)

/-- Erase an STLC type's context index without consuming inference or checking fuel. -/
def AST.resolveType {n} (self : Typ n) : Typ :=
  match self with
  | .TLit => .TLit
  | .TFn input output => .TFn (AST.resolveType input) (AST.resolveType output)

end STLC
