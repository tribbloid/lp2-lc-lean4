import Std

namespace Lp2lc.Active

inductive Which : Type -- only a tag/index for AST of different nature
| typ
| trm
deriving DecidableEq, Repr

def Rep := Which -> Type -- both types and terms are represented by a type family from `Which`
