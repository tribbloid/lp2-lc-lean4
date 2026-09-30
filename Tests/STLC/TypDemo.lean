import «Tests».STLC.ValDemo

namespace Tests.STLC.Sanity
open Lp2lc.Active.STLC

namespace Typ

def tFalse : AST .typ :=
  .TLit

def idFn : AST .typ :=
  .TFn .TLit .TLit

def get1st : AST .typ :=
  .TFn .TLit (.TFn .TLit .TLit)

def apply1stOn2ndFn : AST .typ :=
  .TFn (.TFn .TLit .TLit) (.TFn .TLit .TLit)

end Typ


end Sanity
