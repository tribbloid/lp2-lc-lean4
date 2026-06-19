import «Tests».DTLC.ValDemo

namespace Tests.DTLC.Sanity
open Lp2lc.Active.Util
open Lp2lc.Active.DTLC
open Lp2lc.Active.DTLC.Symbolic

namespace Trm

def vFalse : Trm :=
  .val (.primitive "false")

def vTrue : Trm :=
  .val (.primitive "true")

def idFn : Trm :=
  .val (.fn (fun x => .ref x))

def primitiveIdFn : Trm :=
  .typeHinted
    idFn
    (.depFn .primitive (fun _x => .primitive))

def idFnOnFalse : Trm :=
  .apply idFn vFalse

def primitiveIdFnOnFalse : Trm :=
  .apply primitiveIdFn vFalse

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
    (.apply get1st vFalse)
    vTrue

def get2ndOnTuple : Trm :=
  .apply
    (.apply get2nd vFalse)
    vTrue

def apply1stOn2ndFn : Trm :=
  .val (.fn (fun f =>
      .val (.fn (fun x =>
        .apply
          (.ref f)
          (.ref x)))))

def apply1stOn2ndFnOnTuple : Trm :=
  .apply
    (.apply apply1stOn2ndFn idFn)
    vFalse

def applyidFnOnItself : Trm :=
  .apply idFn idFn

def idFnOnFalse2 : Trm :=
  .apply applyidFnOnItself vFalse

def primitiveTrueFn : Trm :=
  .val
    (.primitiveFn (fun _repr =>
      .val (.primitive "true")))

def primitiveTrueFnOnFalse : Trm :=
  .apply primitiveTrueFn vFalse

namespace TypeHinted

def hintedFalse : Trm :=
  .typeHinted
    (.val (.primitive "false"))
    .primitive

def hintedIdFn : Trm :=
  .typeHinted
    (.val
      (.fn
        (fun x =>
          .typeHinted
            (.ref x)
            .primitive)))
    (.depFn .primitive (fun _x => .primitive))

def hintedIdFnOnFalse : Trm :=
  .typeHinted
    (.apply hintedIdFn hintedFalse)
    .primitive

end TypeHinted

namespace Malformed

def primitiveApply : Trm :=
  .apply vFalse vTrue

def apply1 : Trm :=
  .apply
    (.apply idFn vFalse)
    vTrue

def primitiveFalseAsFn : Trm :=
  .typeHinted
    (.val (.primitive "false"))
    (.depFn .primitive (fun _ => .primitive))

def idFnAsPrimitive : Trm :=
  .typeHinted
    (.val (.fn (fun x => .ref x)))
    .primitive

end Malformed

end Trm

end Sanity
