import Mathlib.Tactic

import «Lp2lc».Active.Shared
import «Lp2lc».Active.STLC

namespace Lp2lc.Active

namespace F

/-
mutual
-- variable (X: Type)

-- inductive Typ {X: Type} : Type
-- | backbone : STLC.Typ (X := Typ (X := X)) -> Typ
-- | bvar : Nat -> Typ
-- | fvar : Var -> Typ
-- deriving Repr

-- end

-- abbrev Trm {X: Type} := STLC.Trm (X := X)

-- inductive TT : Type

-- def b1: Typ (X := TT) := Typ.bvar (X := TT) 0

-- def b2: Typ (X := TT) := Typ.backbone <|
--   STLC.Typ.arrow (X := Typ (X := TT))
--     (STLC.Typ._unknown (X := Typ (X := TT)) b1)
--     (STLC.Typ._unknown (X := Typ (X := TT)) b1)

-- F rule -> LC rule
-- this exampe shoouldl create
-- example : STLC.Typ TT := STLC.Typ.arrow
--   STLC.Typ._unknown (Typ.bvar 0)
--   STLC.Typ._unknown (Typ.bvar 1)

-- SLOP: log the exact type of the previous example at compile-time
-/

end F

end Lp2lc.Active
