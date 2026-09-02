import «Lp2lc».Active.STLC.STLCDef

namespace Tests.STLC.Sanity

open Lp2lc.Active.Util
open Lp2lc.Active.STLC

class TestEnv where
  trm2val : UIdView (λ T => AST.Val { F := T, B := T, D := String })
  trm2valExeCtx : UIdEquiv.Extendable.{3, 3} trm2val

variable [testEnv : TestEnv]

@[reducible] instance refs : TypOrValRefs := { D := String, uid2val := testEnv.trm2val }

end Tests.STLC.Sanity
