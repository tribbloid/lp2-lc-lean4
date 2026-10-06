import «Tests».STLC.ValDemo

namespace Tests.STLC.Sanity

open Lp2lc.Active.STLC
open Lp2lc.Active.Util

namespace Trm
variable (P : Parameters := p0)

def vFalse [Demo P] : Pre.AST P .trm :=
  .val (.lit (Demo.bFalse (P := P)))

def vTrue [Demo P] : Pre.AST P .trm :=
  .val (.lit (Demo.bTrue (P := P)))

def primitiveIdFn [Demo P] : Pre.AST P .trm :=
  .val (.fn .TLit (.mk (λ proxy => .ref proxy .same)))

def primitiveIdFnOnFalse [Demo P] : Pre.AST P .trm :=
  .apply (primitiveIdFn P) (vFalse P)

def get1st [Demo P] : Pre.AST P .trm :=
  .val
    (.fn .TLit
      (.mk (λ first =>
        .val (.fn .TLit (.mk (λ _ => .ref first (.lower .same)))))))

def get2nd [Demo P] : Pre.AST P .trm :=
  .val
    (.fn .TLit
      (.mk (λ _ =>
        .val (.fn .TLit (.mk (λ second => .ref second .same))))))

def get1stOnTuple [Demo P] : Pre.AST P .trm :=
  .apply (.apply (get1st P) (vFalse P)) (vTrue P)

def get2ndOnTuple [Demo P] : Pre.AST P .trm :=
  .apply (.apply (get2nd P) (vFalse P)) (vTrue P)

def primitiveTrueFn [Demo P] : Pre.AST P .trm :=
  .val (.fn .TLit (.mk (λ _ => .val (.lit (Demo.bTrue (P := P))))))

def primitiveTrueFnOnFalse [Demo P] : Pre.AST P .trm :=
  .apply (primitiveTrueFn P) (vFalse P)

namespace FreeCapture

def directRef [Demo P] : Pre.AST P .trm :=
  .ref (Demo.freeSlot (P := P)) .same

def capturedRef [Demo P] : Pre.AST P .trm :=
  .val (.fn .TLit (.mk (λ _ => .ref (Demo.freeSlot (P := P)) (.lower .same))))

def capturedRefOnFalse [Demo P] : Pre.AST P .trm :=
  .apply (capturedRef P) (.val (.lit (Demo.bFalse (P := P))))

end FreeCapture

namespace TypeHinted

def hintedFalse [Demo P] : Pre.AST P .trm :=
  .val (.lit (Demo.bFalse (P := P)))

def hintedIdFn [Demo P] : Pre.AST P .trm :=
  .val (.fn .TLit (.mk (λ proxy => .ref proxy .same)))

def hintedIdFnOnFalse [Demo P] : Pre.AST P .trm :=
  .apply (hintedIdFn P) (hintedFalse P)

end TypeHinted

namespace Malformed

def applyIdFnOnItself [Demo P] : Pre.AST P .trm :=
  .apply (primitiveIdFn P) (primitiveIdFn P)

def idFnOnFalse2 [Demo P] : Pre.AST P .trm :=
  .apply (applyIdFnOnItself P) (vFalse P)

def primitiveApply [Demo P] : Pre.AST P .trm :=
  .apply (vFalse P) (vTrue P)

def apply1 [Demo P] : Pre.AST P .trm :=
  .apply (.apply (primitiveIdFn P) (vFalse P)) (vTrue P)

end Malformed

section generalization

private abbrev boolParameters : Parameters :=
  { B := Bool, I := { Index := Unit, getTRef := λ _ => Bool, inc := id }, index := () }

local instance : Demo boolParameters := ⟨false, true, true⟩

example : (vFalse : AST 0 .trm) = .val (.lit bFalse) := rfl

example : (FreeCapture.directRef : AST 0 .trm) = .ref FreeCapture.freeSlot .same := rfl

example : vFalse (P := boolParameters) = .val (.lit false) := rfl

example : vTrue (P := boolParameters) = .val (.lit true) := rfl

example : Val.idFn boolParameters = .fn .TLit (.mk (λ proxy => .ref proxy .same)) := rfl

example : FreeCapture.directRef boolParameters = .ref (P' := boolParameters) true .same := rfl

example : FreeCapture.capturedRef boolParameters =
    .val (.fn .TLit (.mk (λ _ => .ref (P' := boolParameters) true (.lower .same)))) := rfl

end generalization

end Trm

end Tests.STLC.Sanity
