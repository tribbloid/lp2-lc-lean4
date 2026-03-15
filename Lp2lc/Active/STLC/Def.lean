

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

mutual
-- variable (X: Type)

inductive Typ: Type
| backbone : AnySys.Typ -> Typ
| arrow : Typ -> Typ -> Typ
deriving Repr


-- inductive Typ {X: Type}: Type
-- | _unknown : X -> Typ
-- | backbone : AnySys.Typ -> Typ
-- | arrow : Typ -> Typ -> Typ
-- deriving Repr

end

-- inductive TT : Type

-- STLC rule only
-- example : Typ (X := TT):= Typ.arrow
--   (Typ.backbone AnySys.Typ.all)
--   (Typ.backbone AnySys.Typ.all)

-- SLOP: log the exact type of the previous example at compile-time

end STLC

end Lp2lc.Active
