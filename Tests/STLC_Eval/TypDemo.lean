import «Tests».STLC_Eval.ValDemo

namespace Tests.STLC_Eval.Sanity

open Lp2lc.Active.STLC
open Tests.STLC_Eval.Sanity.Symbolic

namespace Typ

def tPrimitive : Typ :=
  .primitive

def idFn : Typ :=
  .fn .primitive .primitive

end Typ

end Sanity
