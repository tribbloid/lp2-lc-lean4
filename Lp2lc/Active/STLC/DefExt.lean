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
section variable (p : Phase)

mutual
  def Trm.asIn : AST.Trm F → AST.Trm (F.AsIn p)
    | .val value => .val (Val.asIn value)
    | .apply fn arg => .apply (Trm.asIn fn) (Trm.asIn arg)
    | .ref i => .ref { index := i }

  def Typ.asIn : AST.Typ F → AST.Typ (F.AsIn p)
    | .primitive => .primitive
    | .fn tIn tOut => .fn (Typ.asIn tIn) (Typ.asIn tOut)

  def Val.asIn : AST.Val F → AST.Val (F.AsIn p)
    | .primitive repr => .primitive repr
    | .fn body tIn =>
      .fn (λ arg => Trm.asIn (body arg.index)) (Typ.asIn tIn)
end

end
end AST

end
end STLC
