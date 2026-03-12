import Mathlib.Tactic
import «Lp2lc».Active.Shared

namespace Lp2lc.Active

-- System extension, induction rule always cast input into output in either the same system or the most specific system that defined the rule
-- AKA, Typ and Trm are always closed under rules/composition/induction
-- e.g. using STLC rule can cast STLC Typ into STLC Typ, or F Typ into F Typ
-- but using F rule can only cast both STLC/F Typ into F Typ
-- this goes both ways
-- the problem is that theorems are defined for types (including wrapper), not rules
-- Basic (pre)types --

namespace STLC

-- class Sys (X: Type) extends AnySys.Sys X

inductive Typ {X: Type} : Type
| wraps : AnySys.Typ -> Typ
| arrow : X -> X -> Typ
deriving Repr

inductive Trm {X: Type}: Type
| wraps : AnySys.Trm -> Trm
| abs : Typ -> Trm -> Trm
| app : Trm -> Trm -> Trm
deriving Repr

mutual

end STLC

-- namespace F

-- end F

end Lp2lc.Active
