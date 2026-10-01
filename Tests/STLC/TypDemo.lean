import «Tests».STLC.ValDemo

namespace Tests.STLC.Sanity
open Lp2lc.Active.STLC

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
