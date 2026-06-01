import «Tests».DTLC.ValDemo

namespace Tests.DTLC.Sanity
open Lp2lc.Active.Util
open Lp2lc.Active.DTLC
open Lp2lc.Active.DTLC.Symbolic

namespace Trm

def false : Trm :=
  .val (.primitive "false")

def true : Trm :=
  .val (.primitive "true")

def idFn : Trm :=
  .val (.fn (fun x => .ref x))

def idFnOnFalse : Trm :=
  .apply idFn false

def get1st : Trm :=
  .val
    (.fn (fun x =>
      .val
        (.fn (fun _y => .ref x))))

def get2nd : Trm :=
  .val
    (.fn (fun _x =>
      .val
        (.fn (fun y => .ref y))))

def get1stOnTuple : Trm :=
  .apply
    (.apply get1st false)
    true

def get2ndOnTuple : Trm :=
  .apply
    (.apply get2nd false)
    true

def apply1stOn2ndFn : Trm :=
  .val (.fn (fun f =>
      .val (.fn (fun x =>
        .apply
          (.ref f)
          (.ref x)))))

def apply1stOn2ndFnOnTuple : Trm :=
  .apply
    (.apply apply1stOn2ndFn idFn)
    false

def applyidFnOnItself : Trm :=
  .apply idFn idFn

def idFnOnFalse2 : Trm :=
  .apply applyidFnOnItself false

def malformedPrimitiveApply : Trm :=
  .apply false true

def malformedApply1 : Trm :=
  .apply
    (.apply idFn false)
    true

def primitiveTrueFn : Trm :=
  .val
    (.primitiveFn (fun _repr =>
      .val (.primitive "true")))

def primitiveTrueFnOnFalse : Trm :=
  .apply primitiveTrueFn false

def annotatedFalse : Trm :=
  .typeHint
    (.val (.primitive "false"))
    .primitive

def annotatedIdFn : Trm :=
  .typeHint
    (.val
      (.fn
        (fun x =>
          .typeHint
            (.ref x)
            .primitive)))
    (.depFn .primitive (fun _x => .primitive))

def annotatedIdFnOnFalse : Trm :=
  .typeHint
    (.apply annotatedIdFn annotatedFalse)
    .primitive

end Trm

end Sanity
