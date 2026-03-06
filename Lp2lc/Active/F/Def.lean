import Mathlib.Tactic

import «Lp2lc».Active.Shared
import «Lp2lc».Active.STLC

namespace Lp2lc.Active.F

section FixPoint
variable (Peer: Type)

-- Basic types --
inductive STLCTypLike : Type
| all : STLCTypLike -- all-inclusive base type
| arrow : Peer → Peer → STLCTypLike

inductive FTypLike: Type
| bvar : Nat -> FTypLike
| fvar : Var -> FTypLike
| others : STLCTypLike Peer -> FTypLike

end FixPoint
