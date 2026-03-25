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

structure Sys where
  FType: Type u -- F stands for "fixed-point"
  FTerm: Type v

namespace LC -- untyped lambda calculus

inductive Trm (sys: Sys) : Type
| bvar : Nat -> Trm sys -- de Bruijn for bounded variable
| fvar : Var -> Trm sys -- name for free variable (they also have de Bruijn but are quite useless)
| abs : (T: sys.FType) -> (x: sys.FTerm) -> Trm sys -- {x: T => x + 1}
| app : (fn: sys.FTerm) -> (x: sys.FTerm) -> Trm sys -- {fn(x)}

inductive Typ (sys: Sys) : Type
| any : Typ sys -- can bind anything, in type system without subtyping (e.g. LEAN, Haskell) this is usually an internal feature not exposed to user
deriving Repr

end LC

namespace STLC -- simply-typed lambda calculus

abbrev Trm (sys: Sys) := LC.Trm sys

inductive Typ (sys: Sys): Type
| backbone: LC.Typ sys -> Typ sys -- unfold ([a] expression to its parts) should be free (cost no fuel) in induction, but no problem if it cost 1 fuel
| arrow : sys.FType -> sys.FType -> (Typ sys)

-- together they can write any type expression, e.g.

-- namespace Example

  abbrev mk_sys (FType FTerm : Type) : Sys := {
    FType := FType
    FTerm := FTerm
  }

  mutual
    unsafe structure RealTyp : Type where
      self: Typ (mk_sys RealTyp RealTrm)

    unsafe structure RealTrm : Type where
      self: Trm (mk_sys RealTyp RealTrm)
  end

  unsafe def sys : Sys := mk_sys RealTyp RealTrm


--   -- real expressions of RealTyp in STLC
--   example :=
--     let k1 :=  (any : LC.Typ RealTyp) -- LC
--     let k2 := -- STLC(LC)
--       let k1View : Typ RealTyp := Typ.backbone k1
--       Typ.arrow (RealTyp.mk k1View) (RealTyp.mk k1View)
--     let _ : RealTyp := RealTyp.mk k2 -- fixpoint of STLC(LC)
--     Unit

--   -- more generic STLC expressions in any type system that uses STLC as backbone
--   -- namely, mk ensures that Typ F always has a representation in F
--   -- the reverse (F -> Typ F) is not true (e.g. for System F)

--   -- consequently, generic, extendable inductive proof need stronger conditions
--   -- see Example in SysF for what these conditions look like
--   example (F: Type) (mk: Typ F -> F) :=
--     let k1 :=  (any : LC.Typ (F)) -- LC
--     let k2 := -- STLC(LC)
--       let _k1 : Typ F := Typ.backbone k1
--       Typ.arrow (mk _k1) (mk _k1)
--     let _ : F := mk k2 -- fixpoint of STLC(LC)
--     Unit


--   structure RealTrm where
--     self: Trm RealTyp RealTrm
--   deriving Repr

--   example (mkT : Trm RealTyp RealTrm -> RealTrm) (mkY : Typ RealTyp -> RealTyp) :=
--     let t1 := (any : LC.Typ RealTyp)
--     let k1 := mkY (Typ.backbone t1)
--     let e1 := (LC.Trm.abs k1 (mkT (Trm.backbone (LC.Trm.bvar 0))) : LC.Trm RealTyp RealTrm)
--     let e2 := Trm.backbone e1
--     let _ : RealTrm := mkT e2
--     Unit

-- end Example

end STLC

-- namespace SysF

-- inductive Typ (F: Type): Type
-- | backbone: STLC.Typ F -> Typ F
-- | bvar : Nat -> Typ F -- binded type variable by De-Bruijn index
-- | fvar : Var -> Typ F -- free type variable by name
-- deriving Repr

-- inductive Trm (F: Type) (G: Type) : Type
-- | backbone : STLC.Trm F G -> Trm F G
-- | tabs : F -> G -> Trm F G
-- | tapp : G -> F -> Trm F G
-- deriving Repr

-- end SysF

end Lp2lc.Active
