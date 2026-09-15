import «Lp2lc».Active.STLC.STLCDef

namespace Tests.STLC.Sanity

open Lp2lc.Active.Util
open Lp2lc.Active.STLC


/-
FIXME: this class can have a concrete, opaque implementation, which index each AST by its hash

once the implementation is ready, all the assertion in `TrmSpec` can be replaced by a single line of #guard
-/

/-- Supplies the shared reference view and runtime value context used by STLC tests. -/
class TestEnv where
  trm2either : UIdRefs (λ C =>
    let P : Parameters := { C := C, D := String }
    AST.Val P ⊕ AST.Typ P)
  trm2valExe : {v : trm2either.Lesser _ // v.upcastV.toFun = Sum.inl}
  trm2valExeCtx : KVEquiv trm2valExe.val.toKVRefs

variable [testEnv : TestEnv]

@[reducible] instance refs : HasUId2Any :=
  { D := String, uid2any := testEnv.trm2either }

@[simp]
theorem trm2valLookup
    (receipt : {uid // testEnv.trm2valExe.val.ev uid}) :
    refs.uid2any.get receipt.val = .inl (testEnv.trm2valExe.val.get receipt) :=
  (testEnv.trm2valExe.val.equivariance receipt).symm.trans
    (congrFun testEnv.trm2valExe.property _)

end Tests.STLC.Sanity
