import Mathlib.Tactic
import «Lp2lc».Active.Shared

namespace Lp2lc.Active

namespace Exp

inductive TypLike (X: Type) : Type
| _unknown: X -> TypLike X
| all : TypLike X -- all-inclusive base type
| arrow : X -> X -> TypLike X
deriving Repr

end Exp
---
namespace STLC

class Sys

mutual
-- System extension, induction rule always cast input into output in either the same system or the most specific system that defined the rule
-- AKA, Typ and Trm are always closed under rules/composition/induction
-- e.g. using STLC rule can cast STLC Typ into STLC Typ, or F Typ into F Typ
-- but using F rule can only cast both STLC/F Typ into F Typ
-- this goes both ways
-- the problem is that theorems are defined for types (including wrapper), not rules
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

abbrev Typ {X: Type} := { T : TypLike (X := X) // ∀ x : X, T ≠ TypLike._unknown x }
abbrev Trm {X: Type} := { T : TrmLike (X := X) // ∀ x : X, T ≠ TrmLike._unknown x }

end STLC

namespace F

class Sys extends STLC.Sys

end F

end Lp2lc.Active
