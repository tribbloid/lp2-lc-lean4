import «Tests».DTLC.ValDemo

namespace Tests.DTLC.Sanity
open Lp2lc.Active.Util
open Lp2lc.Active.DTLC
open Lp2lc.Active.DTLC.Symbolic

namespace Trm

def false : Trm String :=
  .val (.primitive "false")

def true : Trm String :=
  .val (.primitive "true")

def idFn : Trm String :=
  .val (.fn (fun x => .ref x))

def idFnOnFalse : Trm String :=
  .apply idFn false

def get1st : Trm String :=
  .val
    (.fn (fun x =>
      .val
        (.fn (fun _y => .ref x))))

def get2nd : Trm String :=
  .val
    (.fn (fun _x =>
      .val
        (.fn (fun y => .ref y))))

def get1stOnTuple : Trm String :=
  .apply
    (.apply get1st false)
    true

def get2ndOnTuple : Trm String :=
  .apply
    (.apply get2nd false)
    true

def apply1stOn2ndFn : Trm String :=
  .val (.fn (fun f =>
      .val (.fn (fun x =>
        .apply
          (.ref f)
          (.ref x)))))

def apply1stOn2ndFnOnTuple : Trm String :=
  .apply
    (.apply apply1stOn2ndFn idFn)
    false

def applyidFnOnItself : Trm String :=
  .apply idFn idFn

def idFnOnFalse2 : Trm String :=
  .apply applyidFnOnItself false

def primitiveTrueFn : Trm String :=
  .val
    (.primitiveFn (fun _repr =>
      .val (.primitive "true")))

def primitiveTrueFnOnFalse : Trm String :=
  .apply primitiveTrueFn false

namespace TypeHinted

def hintedFalse : Trm String :=
  .typeHinted
    (.val (.primitive "false"))
    .primitive

def hintedIdFn : Trm String :=
  .typeHinted
    (.val
      (.fn
        (fun x =>
          .typeHinted
            (.ref x)
            .primitive)))
    (.depFn .primitive (fun _x => .primitive))

def hintedIdFnOnFalse : Trm String :=
  .typeHinted
    (.apply hintedIdFn hintedFalse)
    .primitive

end TypeHinted

namespace Malformed

def primitiveApply : Trm String :=
  .apply false true

def apply1 : Trm String :=
  .apply
    (.apply idFn false)
    true

def primitiveFalseAsFn : Trm String :=
  .typeHinted
    (.val (.primitive "false"))
    (.depFn .primitive (fun _ => .primitive))

def idFnAsPrimitive : Trm String :=
  .typeHinted
    (.val (.fn (fun x => .ref x)))
    .primitive

end Malformed

end Trm

end Sanity
