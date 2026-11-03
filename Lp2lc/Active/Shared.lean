import Std

namespace Lp2lc.Active

/-- Tags the syntactic families (types, values, pure expressions, and terms) that a shared representation can expose. -/
inductive Label : Type -- only a tag/index for AST of different nature
/-- type like `Int` -/
| typ
/-- value like `1` -/
| val
/-- A pure expression with a stable/cached result, like a pure expression in Lean or a stable Scala/DOT path.
Dependent types may refer only to this family; evaluation resolves it to an actual value. -/
| pure
/-- All terms, including pure and impure expressions such as `randn()`. -/ -- should it be "term"?
| trm

deriving DecidableEq, Repr

def Rep := (label : Label) → Type -- Each syntactic family is represented by a type from `Label`.
