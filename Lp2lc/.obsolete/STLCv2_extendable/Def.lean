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
| backbone: LC.Typ F -> Typ F -- unfold ([a] expression to its parts) should be free (cost no fuel) in induction, but no problem if it cost 1 fuel
| arrow : F -> F -> (Typ F)
deriving Repr
-- together they can write any type expression, e.g.

namespace Example

  structure RealTyp where
    self: Typ RealTyp -- unfold[a] should also be free, mk (parts to expression) cost fuel

  -- real expressions of RealTyp in STLC
  example :=
    let k1 :=  (.all : LC.Typ RealTyp) -- LC
    let k2 := -- STLC(LC)
      let k1View : Typ RealTyp := Typ.backbone k1
      Typ.arrow (RealTyp.mk k1View) (RealTyp.mk k1View)
    let _ : RealTyp := RealTyp.mk k2 -- fixpoint of STLC(LC)
    Unit

  -- more generic STLC expressions in any type system that uses STLC as backbone
  -- namely, mk ensures that Typ F always has a representation in F
  -- the reverse (F -> Typ F) is not true (e.g. for System F)

  -- consequently, generic, extendable inductive proof need stronger conditions
  -- see Example in SysF for what these conditions look like
  example (F: Type) (mk: Typ F -> F) :=
    let k1 :=  (.all : LC.Typ (F)) -- LC
    let k2 := -- STLC(LC)
      let _k1 : Typ F := Typ.backbone k1
      Typ.arrow (mk _k1) (mk _k1)
    let _ : F := mk k2 -- fixpoint of STLC(LC)
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

  lemma bvarLemma (_F : Type) (_n : Nat) : SomeBullshitConjecture := sorry
  lemma fvarLemma (_F : Type) (_x : Var) : SomeBullshitConjecture := sorry

  -- assuuming you have a generic, extendable theorem for STLC Typ:
  lemma stlcLemma (F : Type) -- THIS should NOT happen.
    (mk : STLC.Typ F -> F)
    (unfold : F -> (STLC.Typ F ⊕' SomeBullshitConjecture)) -- contains a shortcut to the conjecture directly
    (v: F)
    : SomeBullshitConjecture :=
      sorry --

  theorem sysFCorollary (F : Type)
    (mk : Typ F -> F)
    (unfold : F -> (Typ F ⊕' SomeBullshitConjecture)) -- contains a shortcut to the conjecture directly
    (v: F)
    : SomeBullshitConjecture :=
      stlcLemma F
        (fun t => mk (.backbone t))
        (fun real =>
          match unfold real with
          | .inl (.backbone t) => .inl t
          | .inl (.bvar n) => .inr (bvarLemma F n)
          | .inl (.fvar x) => .inr (fvarLemma F x)
          | .inr p => .inr p)
        v

end Example

end SysF

end Lp2lc.Active
