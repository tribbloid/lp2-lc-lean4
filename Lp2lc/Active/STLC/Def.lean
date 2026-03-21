

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

namespace LC -- untyped lambda calculus

inductive Typ (F: Type): Type -- F stands for "fixed-point"
| leaks: F -> Typ F -- AKA wildcard, others, unknown, can be any type symbol
| all : Typ F
deriving Repr

end LC

namespace STLC -- simply-typed lambda calculus

inductive Typ (F: Type): Type
| backbone: LC.Typ F -> Typ F
| arrow : Typ F -> (Typ F) -> (Typ F)
deriving Repr
-- together they can write any type expression, e.g.

namespace Example

  structure RealTyp where -- so this is the actual bottleneck?
    self: Typ RealTyp

  -- real expressions of RealTyp in STLC
  example :=
    let k1 :=  (.all : LC.Typ RealTyp) -- LC
    let k2 := -- STLC(LC)
      let k1View := .backbone k1
      Typ.arrow k1View k1View
    let _ := LC.Typ.leaks (RealTyp.mk k2) -- LC(STLC(LC))
    Unit

  -- more generic STLC expressions in any type system that uses STLC as backbone
  -- namely, mk ensures that Typ F always has a representation in F
  -- the reverse (F -> Typ F) is not true (e.g. for System F)

  -- consequently, generic, extendable inductive proof need stronger conditions
  -- see Example in SysF for what these conditions look like
  example (F: Type) (mk: Typ F -> F) :=
    let k1 :=  (.all : LC.Typ (F)) -- LC
    let k2 := -- STLC(LC)
      let k1View := .backbone k1
      Typ.arrow k1View k1View
    let _ := LC.Typ.leaks (mk k2) -- LC(STLC(LC))
    Unit

end Example

end STLC

namespace SysF

inductive Typ (F: Type): Type
| backbone: STLC.Typ F -> Typ F
| bvar : Nat -> Typ F -- binded type variable by De-Bruijn index
| fvar : Var -> Typ F -- free type variable by name
deriving Repr

namespace Example

def SomeBullshitConjecture : Prop := sorry

-- assuuming you have a generic, extendable theorem for STLC Typ:
theorem stlcProof (F : Type)
  (mk : STLC.Typ F -> F)
  (unmk : F -> STLC.Typ F) : STLC.Typ F -> SomeBullshitConjecture :=
  sorry

theorem bvarLemma (_F : Type) (_n : Nat) : SomeBullshitConjecture := sorry
theorem fvarLemma (_F : Type) (_x : Var) : SomeBullshitConjecture := sorry

theorem sysFCorollary (F : Type)
  (mk : Typ F -> F)
  (unmk : F -> Typ F) : Typ F -> SomeBullshitConjecture
  | .bvar n => bvarLemma F n
  | .fvar x => fvarLemma F x
  | .backbone t =>
    let subMk (typ: STLC.Typ F): F := mk (Typ.backbone typ)
    let subUnmk(real: F): STLC.Typ F :=
      let typ := unmk real

      sorry
    stlcProof F subMk subUnmk t
    -- let t' := unmk t
    -- stlcProof F unmk t


end Example

end SysF

end Lp2lc.Active
