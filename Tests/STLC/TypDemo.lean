import «Tests».STLC.ValDemo

namespace Tests.STLC.Sanity
open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

namespace Typ

def false : Typ :=
  .primitive

def idFn : Typ :=
  .fn .primitive .primitive

def get1st : Typ :=
  .fn .primitive (.fn .primitive .primitive)

end Typ


end Sanity
