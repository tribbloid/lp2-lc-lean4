import «Tests».STLC.ValDemo

namespace Tests.STLC.Sanity
open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

variable [testEnv : TestEnv]

namespace Typ

def tFalse : Typ :=
  .TLit

def idFn : Typ :=
  .TFn .TLit .TLit

def get1st : Typ :=
  .TFn .TLit (.TFn .TLit .TLit)

def apply1stOn2ndFn : Typ :=
  .TFn (.TFn .TLit .TLit) (.TFn .TLit .TLit)

end Typ


end Sanity
