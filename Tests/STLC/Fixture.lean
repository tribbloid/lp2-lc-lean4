import «Lp2lc».Active.STLC.STLCDef

namespace Tests.STLC.Sanity

open Lp2lc.Active.Util
open Lp2lc.Active.STLC

/-- Supplies the shared reference view and runtime value context used by STLC tests. -/
class TestEnv where
  trm2either : UIdRefs (λ C =>
    let P : Parameters := { C := C, D := String }
    AST.Val P ⊕ AST.Typ P)
  trm2valExe : trm2either.Lesser ⟨Sum.inl, λ _left _right => Sum.inl.inj⟩
  trm2valExeCtx : RefEquiv.{3} trm2valExe.toRefs

variable [testEnv : TestEnv]

@[reducible] instance refs : HasUId2Any :=
  { D := String, uid2any := testEnv.trm2either }

@[simp]
theorem trm2valLookup
    (receipt : {uid // testEnv.trm2valExe.ev uid}) :
    refs.uid2any.get receipt.val = .inl (testEnv.trm2valExe.get receipt) :=
  (testEnv.trm2valExe.equivariance receipt).symm

end Tests.STLC.Sanity
