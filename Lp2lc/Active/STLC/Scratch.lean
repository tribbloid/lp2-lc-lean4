

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

namespace CombineIncompleteMatch

-- SLOP: demonstrate example of combining 2 props into 1

inductive Thing: Type
| rock: Thing
| swallow: Thing
| bat: Thing
| dog: Thing

def isBird (f: Thing): Prop :=
  match f with
  | .rock => False
  | .swallow => True
  | .bat => False
  | .dog => False

def isMammal (f: Thing): Prop :=
  match f with
  | .rock => False
  | .swallow => False
  | .bat => True
  | .dog => True

def isAnimal (f: Thing): Prop := isBird f ∨ isMammal f

end CombineIncompleteMatch

end Lp2lc.Active
