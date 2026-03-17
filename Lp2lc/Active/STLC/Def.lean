

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

namespace LC -- lambda calculus, untyped

inductive _Typ (TT: Type): Type
| others: TT -> _Typ TT
| all : _Typ TT

-- def Typ (TT: Type) :=
--   {t : _Typ TT // t = .all}

def Typ (TT: Type): Type :=
  {t : _Typ TT // ∀ x, t ≠ .others x}

end LC

namespace STLC

inductive _Typ (TT: Type): Type
| others: TT -> _Typ TT
| base: LC._Typ TT -> _Typ TT
| arrow : (_Typ TT) -> (_Typ TT) -> (_Typ TT)

def Typ (TT: Type): Type :=
  {t : _Typ TT //
    match t with
    | .others _ => False
    | .base _ => True
    | .arrow _ _ => True
  }

def t0 := LC._Typ.all Int
#check t0

def examples (D: Type) :=

  let t0 := LC._Typ.all

  let t1: LC.Typ D := LC._Typ.all D
  let t2: LC.Typ D := LC._Typ.all D

  sorry



end STLC

end Lp2lc.Active
