import «Tests».DSub.ValDemo

namespace Tests.DSub.Sanity
open Lp2lc.Active.DSub

namespace Typ

def tFalse : AST 0 .typ :=
  .TLit

def idFn {n : Nat} : AST n .typ :=
  .TFn .TLit (.mk (λ _ => .TLit))

def get1st : AST 0 .typ :=
  .TFn .TLit (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit)))))

def apply1stOn2ndFn : AST 0 .typ :=
  .TFn (.TFn .TLit (.mk (λ _ => .TLit))) (.mk (λ _ => (.TFn .TLit (.mk (λ _ => .TLit)))))

namespace InDSub

variable {n : Nat}

def boolType : Typ n :=
  .TMember .TLit .TLit

def fnType : Typ n :=
  .TMember idFn idFn

def boundedMember : Typ n :=
  .TMember .TBot .TLit

def lowerBoundedMember : Typ n :=
  .TMember .TLit .TTop

def abstractMember : Typ n :=
  .TMember .TBot .TTop

def dependentId : Typ n :=
  .TFn abstractMember (.mk (λ x =>
    .TFn (.TSel (.ref x .same)) (.mk (λ _ => .TSel (.ref x (.lower .same))))))

def dependentType : Typ n :=
  .TFn abstractMember (.mk (λ x =>
    let selected := .TSel (.ref x .same)
    .TMember selected selected))

def capturedId : Typ n :=
  .TFn abstractMember (.mk (λ x =>
    .TFn abstractMember (.mk (λ _ =>
      .TFn (.TSel (.ref x (.lower .same))) (.mk (λ _ =>
        .TSel (.ref x (.lower (.lower .same)))))))))

def boundedDependentId : Typ n :=
  .TFn boundedMember (.mk (λ x =>
    .TFn (.TSel (.ref x .same)) (.mk (λ _ => .TLit))))

def selectedBool : Typ n :=
  .TSel (.typeDef .TLit)

def selectedFn : Typ n :=
  .TSel (.typeDef idFn)

end InDSub

end Typ

end Sanity
