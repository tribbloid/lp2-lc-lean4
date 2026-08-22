import «Tests».STLC.ValDemo

namespace Tests.STLC.Sanity
open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

variable [testEnv : TestEnv]

namespace Typ

def tFalse : Typ :=
  .primitive

def idFn : Typ :=
  .fn .primitive .primitive

def get1st : Typ :=
  .fn .primitive (.fn .primitive .primitive)

def apply1stOn2ndFn : Typ :=
  .fn (.fn .primitive .primitive) (.fn .primitive .primitive)

end Typ


end Sanity
