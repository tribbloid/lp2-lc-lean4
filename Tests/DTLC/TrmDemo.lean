import «Tests».DTLC.ValDemo

namespace Tests.DTLC.Sanity
open Lp2lc.Active.Util
open Lp2lc.Active.DTLC

namespace Trm

def false : TrmAST :=
  .val (.primitive "false")

def true : TrmAST :=
  .val (.primitive "true")

def idFn : TrmAST :=
  .val (.fn (body := fun x => .ref x))

def idFnOnFalse : TrmAST :=
  .apply idFn false

def get1st : TrmAST :=
  .val
    (.fn (body := fun x =>
      .val
        (.fn (body := fun _y => .ref x))))

def get2nd : TrmAST :=
  .val
    (.fn (body := fun _x =>
      .val
        (.fn (body := fun y => .ref y))))

def get1stOnTuple : TrmAST :=
  .apply
    (.apply get1st false)
    true

def get2ndOnTuple : TrmAST :=
  .apply
    (.apply get2nd false)
    true

def apply1stOn2ndFn : TrmAST :=
  .val (.fn (body := fun f =>
      .val (.fn (body := fun x =>
        .apply
          (.ref f)
          (.ref x)))))

def apply1stOn2ndFnOnTuple : TrmAST :=
  .apply
    (.apply apply1stOn2ndFn idFn)
    false

def applyidFnOnItself : TrmAST :=
  .apply idFn idFn

def idFnOnFalse2 : TrmAST :=
  .apply applyidFnOnItself false

def malformedPrimitiveApply : TrmAST :=
  .apply false true

def annotatedFalse : TrmAST :=
  .val (.primitive "false") (some .primitive)

def annotatedIdFn : TrmAST :=
  .val
    (.fn
      (body := fun x => .ref x (some .primitive)))
    (some (.depFn .primitive (fun _x => .primitive)))

def annotatedIdFnOnFalse : TrmAST :=
  .apply annotatedIdFn annotatedFalse (some .primitive)

end Trm

end Sanity
