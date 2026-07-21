import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util
import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active

namespace STLC

/- Shared STLC syntax family, currently exposing function types over the common representation. -/
open Lp2lc.Active.Util
section variable {F : Free}

namespace AST

def Trm.phase1 (v: AST.Trm F): AST.Trm (F.For .compilation) :=
  match v with
  | .val value => .val (val.phase1 value)
  | .apply fn arg => .apply (Trm.phase1 fn) (Trm.phase1 arg)
  | .ref i => .ref { index := i }
where
  Typ.phase1 : AST.Typ F → AST.Typ (F.For .compilation)
    | .primitive => .primitive
    | .fn tIn tOut => .fn (Typ.phase1 tIn) (Typ.phase1 tOut)

  val.phase1 : AST.Val F → AST.Val (F.For .compilation)
    | .primitive repr => .primitive repr
    | .fn body tIn =>
      .fn (λ arg => Trm.phase1 (body arg.index)) (Typ.phase1 tIn)


end AST

end
end STLC
