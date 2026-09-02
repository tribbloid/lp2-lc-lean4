import «Lp2lc».Active.STLC.STLCDef

namespace Tests.STLC.Sanity

open Lp2lc.Active.Util
open Lp2lc.Active.STLC

/-- Supplies the shared reference view and runtime value context used by STLC tests. -/
class TestEnv where
  trm2either : UIdView (λ C =>
    let P : Parameters := { C := C, D := String }
    AST.Val P ⊕ AST.Typ P)
  trm2valExeCtx : UIdEquiv.Lesser (base := trm2either)
    (Sum.inl : AST.Val { C := trm2either.UId, D := String } →
      AST.Val { C := trm2either.UId, D := String } ⊕
        AST.Typ { C := trm2either.UId, D := String })

variable [testEnv : TestEnv]

@[reducible] instance refs : TypOrValRefs :=
  { D := String, uid2either := testEnv.trm2either }

@[simp]
theorem trm2valLookup
    (receipt : {uid // testEnv.trm2valExeCtx.ev uid}) :
    refs.uid2either.get receipt.val = .inl (testEnv.trm2valExeCtx.get receipt) :=
  (testEnv.trm2valExeCtx.equivariance receipt).symm

end Tests.STLC.Sanity
