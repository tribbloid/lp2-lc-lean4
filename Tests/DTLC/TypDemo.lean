import «Tests».DTLC.ValDemo

namespace Tests.DTLC.Sanity
open Lp2lc.Active.DTLC

namespace Typ

def tFalse : AST 0 .typ :=
  .TLit

def idFn : AST 0 .typ :=
  .TFn .TLit (.mk (λ _ => .TLit))

def get1st : AST 0 .typ :=
  .TFn .TLit (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit)))))

def apply1stOn2ndFn : AST 0 .typ :=
  .TFn (.TFn .TLit (.mk (λ _ => .TLit))) (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit)))))

end Typ

end Sanity
