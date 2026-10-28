import «Tests».STLC_minimal.ValDemo

namespace Tests.STLC_minimal.Sanity
open Lp2lc.Active.STLC_minimal

namespace Typ

def tFalse : AST 0 .typ :=
  .TLit

def idFn : AST 0 .typ :=
  .TFn .TLit .TLit

def get1st : AST 0 .typ :=
  .TFn .TLit (.TFn .TLit .TLit)

def apply1stOn2ndFn : AST 0 .typ :=
  .TFn (.TFn .TLit .TLit) (.TFn .TLit .TLit)

end Typ

end Sanity
