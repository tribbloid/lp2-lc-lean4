import Mathlib.Tactic
import «Lp2lc».Active.Shared

namespace Lp2lc.Active

structure BiMap (α β : Type) where
  fwd : α -> β
  inv : β -> α

-- System extension, induction rule always cast input into output in either the same system or the most specific system that defined the rule
-- AKA, Typ and Trm are always closed under rules/composition/induction
-- e.g. using STLC rule can cast STLC Typ into STLC Typ, or F Typ into F Typ
-- but using F rule can only cast both STLC/F Typ into F Typ
-- this goes both ways
-- the problem is that theorems are defined for types (including wrapper), not rules
-- Basic (pre)types --

namespace LC -- untyped lambda calculus

inductive Typ
  (F: Type) --AKA wildcard, others, unknown, can be any type symbol
  : Type -- F stands for "fixed-point"
| all : Typ F
deriving Repr

end LC

namespace STLC -- simply-typed lambda calculus

inductive Typ (F: Type): Type
| backbone: LC.Typ F -> Typ F -- should cost 0 fuel in induction, but no problem if it cost 1 fuel
| arrow : F -> F -> (Typ F)
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


theorem bvarLemma (_F : Type) (_n : Nat) : SomeBullshitConjecture := sorry
theorem fvarLemma (_F : Type) (_x : Var) : SomeBullshitConjecture := sorry

namespace P1

-- assuuming you have a generic, extendable theorem for STLC Typ:
theorem stlcProof (F : Type)
  (view : BiMap (STLC.Typ F) F) -- TODO: not sure if ⊕' can be moved to call-site
  : STLC.Typ F -> SomeBullshitConjecture :=
  sorry


theorem sysFCorollary (F : Type)
  (mk : Typ F -> F)
  (unmk : F -> Typ F)
  : Typ F -> SomeBullshitConjecture
  | .bvar n => bvarLemma F n
  | .fvar x => fvarLemma F x
  | .backbone t =>
    let view : BiMap (STLC.Typ F) F := {
      fwd := fun typ => mk (Typ.backbone typ)
      inv := fun real =>
        let typ := unmk real

        sorry
    }
    stlcProof F view t
    -- let t' := unmk t
    -- stlcProof F unmk t

end P1

namespace P2

-- assuuming you have a generic, extendable theorem for STLC Typ:
theorem stlcProof (F : Type)
  (_view : BiMap (STLC.Typ F) F) -- assuming that both to_fun and inv_fun are total and terminating
  (_v : F)
  : SomeBullshitConjecture :=
  sorry

-- assuuming you have a generic, extendable theorem for STLC Typ:
theorem stlcProofRelaxed (F : Type) -- THIS should NOT happen.
  (mk : STLC.Typ F -> F)
  (unmk : F -> (STLC.Typ F ⊕' SomeBullshitConjecture)) -- contains a shortcut to the conjecture directly
  (v: F)
  : SomeBullshitConjecture :=
    match unmk v with
    | .inl (t: STLC.Typ F) =>
      stlcProof F {
        fwd := mk
        inv := fun real =>
          match unmk real with
          | .inl t' => t'
          | .inr _ => t
          -- t
      }
        (mk t)
    | .inr p => p


theorem sysFCorollary (F : Type)
  (mk : BiMap (Typ F) F)
  (v: F)
  : SomeBullshitConjecture :=
    match mk.inv v with
    | .bvar n => bvarLemma F n
    | .fvar x => fvarLemma F x
    | .backbone (t: STLC.Typ F) =>
      let view : BiMap (STLC.Typ F) F := {
        fwd := fun typ => mk.fwd (Typ.backbone typ)
        inv := fun real =>
          match mk.inv real with
          | .backbone t' => t'
          | .bvar _ => t
          | .fvar _ => t
      }
      stlcProof F view v

theorem sysFCorollary2 (F : Type)
  (mk : BiMap (Typ F) F)
  (v: F)
  : SomeBullshitConjecture :=
    let view : BiMap (STLC.Typ F) F := {
        fwd := fun typ => mk.fwd (Typ.backbone typ)
        inv := fun real =>
          match mk.inv real with
          | .backbone t' => t'
          | .bvar n => bvarLemma F n
          | .fvar x => fvarLemma F x
      }
    stlcProof F view v

w
end P2


end Example

end SysF

end Lp2lc.Active
