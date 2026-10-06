import «Tests».STLC.ValDemo

namespace Tests.STLC.Sanity
open Lp2lc.Active.STLC
open Lp2lc.Active.Util

namespace Typ
variable (P : Parameters := p0)

def tFalse [Demo P] : Pre.AST P .typ :=
  .TLit

def idFn [Demo P] : Pre.AST P .typ :=
  .TFn .TLit .TLit

def get1st [Demo P] : Pre.AST P .typ :=
  .TFn .TLit (.TFn .TLit .TLit)

def apply1stOn2ndFn [Demo P] : Pre.AST P .typ :=
  .TFn (.TFn .TLit .TLit) (.TFn .TLit .TLit)

section generalization

example : (idFn : AST 0 .typ) = .TFn .TLit .TLit := rfl

example {P : Parameters} [Demo P] :
    get1st P = .TFn .TLit (.TFn .TLit .TLit) := rfl

end generalization

end Typ

end Sanity
