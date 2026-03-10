import Mathlib.Tactic
import «Lp2lc».Active.Shared

namespace Lp2lc.Active.STLCv2

class Sys (Typ Trm: Type) where
all: Typ
arrow: Typ -> Typ -> Typ
bvar : Nat → Trm
fvar : Var → Trm
abs : Typ → Trm → Trm
app : Trm → Trm → Trm



end Lp2lc.Active.STLCv2
