import Std

namespace Lp2lc.Active

/-- Tags the syntactic families (types, terms, values) that a shared representation can expose. -/
inductive Label : Type -- only a tag/index for AST of different nature
/-- type like `Int` -/
| typ
/-- value like `1` -/
| val
/-- pure term expression with a stable/cached execution result, like a pure expression in Lean or a stable path in Scala/DOT
this is the only definition where dependent types can depends on, but evaluation shall not return it (instead of normalising further) -/
| pure
/-- all term expression, pure or unpure, like `randn()`-/ -- should it be "term"?
| trm

deriving DecidableEq, Repr

def Rep := (label : Label) → Type -- both types and terms are represented by a type family from `Label`
