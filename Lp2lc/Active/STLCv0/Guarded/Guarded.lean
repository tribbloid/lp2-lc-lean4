import Mathlib.Tactic
import Iris.Algebra.OFE
import «Lp2lc».Active.Shared

namespace Lp2lc.Active.STLC

namespace Guarded

open Iris

inductive TypLike (Peer : Type _) : Type _ where
| typ_all : TypLike Peer
| typ_arrow : Later Peer → Later Peer → TypLike Peer

inductive TrmLike (Typ Peer : Type _) : Type _ where
| bvar : Nat → TrmLike Typ Peer
| fvar : Var → TrmLike Typ Peer
| abs : Typ → Later Peer → TrmLike Typ Peer
| app : Later Peer → Later Peer → TrmLike Typ Peer

abbrev TypBody := TypLike

abbrev TrmBody (Typ : Type _) := TrmLike Typ

end Guarded

end Lp2lc.Active.STLC
