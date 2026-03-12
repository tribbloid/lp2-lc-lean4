import Mathlib.Tactic
import «Lp2lc».Active.Shared

namespace Lp2lc.Active.STLC

mutual
-- Basic (pre)types --
inductive Typ {X: Type} : Type
| _unknown: X -> Typ
| all : Typ -- all-inclusive base type
| arrow : Typ -> Typ -> Typ
deriving DecidableEq, Repr

-- Defining (pre)terms by recursion --
inductive Trm {X: Type} : Type
| _unknown: X -> Trm
| bvar : Nat → Trm
| fvar : Var → Trm
| abs : Typ → Trm → Trm
| app : Trm → Trm → Trm
deriving DecidableEq, Repr
end

abbrev known_typ {X: Type} : Type := { T : Typ (X := X) // ∀ x : X, T ≠ Typ._unknown x }


end Lp2lc.Active.STLC
