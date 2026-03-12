import Mathlib.Tactic
import «Lp2lc».Active.Shared

namespace Lp2lc.Active.STLC

mutual
-- Basic (pre)types --
inductive TypLike {X: Type} : Type
| _unknown: X -> TypLike
| all : TypLike -- all-inclusive base type
| arrow : TypLike -> TypLike -> TypLike
deriving Repr

-- Defining (pre)terms by recursion --
inductive TrmLike {X: Type} : Type
| _unknown: X -> TrmLike
| bvar : Nat → TrmLike
| fvar : Var → TrmLike
| abs : TypLike → TrmLike → TrmLike
| app : TrmLike → TrmLike → TrmLike
deriving Repr
end

abbrev Typ {X: Type} : Type := { T : TypLike (X := X) // ∀ x : X, T ≠ TypLike._unknown x }
abbrev Trm {X: Type} : Type := { T : TrmLike (X := X) // ∀ x : X, T ≠ TrmLike._unknown x }

end Lp2lc.Active.STLC
