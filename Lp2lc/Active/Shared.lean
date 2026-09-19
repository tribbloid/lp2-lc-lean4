import Std

namespace Lp2lc.Active

/-- Tags the syntactic families (types, terms, values) that a shared representation can expose. -/
inductive Label : Type -- only a tag/index for AST of different nature
| typ
| trm
| val
deriving DecidableEq, Repr

def Rep := (label : Label) → Type -- both types and terms are represented by a type family from `Label`
