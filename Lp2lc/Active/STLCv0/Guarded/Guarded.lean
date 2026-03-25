import Mathlib.Tactic
import Iris.Algebra.OFE
import «Lp2lc».Active.Shared

namespace Lp2lc.Active.STLC

namespace Guarded

open Iris

inductive Typ (Peer : Type _) : Type _ where
| typ_all : Typ Peer
| typ_arrow : Later Peer → Later Peer → Typ Peer

inductive Trm (Typ Peer : Type _) : Type _ where
| bvar : Nat → Trm Typ Peer
| fvar : Var → Trm Typ Peer
| abs : Typ → Later Peer → Trm Typ Peer
| app : Later Peer → Later Peer → Trm Typ Peer

end Guarded

end Lp2lc.Active.STLC
