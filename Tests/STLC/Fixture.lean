import «Lp2lc».Active.STLC.STLCDef

namespace Tests.STLC.Sanity

open Lp2lc.Active.Util
open Lp2lc.Active.STLC

class TestEnv where
  trm2val : UIdView (λ T => AST.Val { C := T, D := String })
  trm2valCtx : UIdEquiv.Extendable.{3, 3}
    (VK := λ T => AST.Val { C := T, D := String }) (base := trm2val)

variable [testEnv : TestEnv]

@[reducible] instance refs : ExeRefs := { D := String, uid2val := testEnv.trm2val }

end Tests.STLC.Sanity
