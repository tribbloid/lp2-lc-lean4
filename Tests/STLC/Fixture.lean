import «Lp2lc».Active.STLC.STLCDef

namespace Tests.STLC.Sanity

open Lp2lc.Active.Util
open Lp2lc.Active.STLC

class TestEnv where
  trm2val : UIdView (λ T => ∀ {B : UIdU}, AST.Val { F := T, B := B, D := String })
  trm2valExeCtx : UIdEquiv.Extendable.{3, 3}
    (VK := λ T => AST.Val { F := T, B := trm2val.UId, D := String })
    (base := { UId := trm2val.UId, get := λ uid => trm2val.get uid (B := trm2val.UId) })

variable [testEnv : TestEnv]

@[reducible] instance refs : ExeRefs := { D := String, uid2val := testEnv.trm2val }

end Tests.STLC.Sanity
