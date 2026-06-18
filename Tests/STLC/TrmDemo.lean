import «Tests».STLC.ValDemo

namespace Tests.STLC.Sanity
open Lp2lc.Active.Util
open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

namespace Trm

def vFalse : Trm :=
  .val (.primitive "false") .primitive

def vTrue : Trm :=
  .val (.primitive "true") .primitive

def idFn : Trm :=
  .val
    (.fn (fun x => .ref x))
    (.fn .primitive .primitive)

def idFnOnFalse : Trm :=
  .apply idFn vFalse

def get1st : Trm :=
  .val
    (.fn (fun x =>
      .val
        (.fn (fun _y => .ref x))
        (.fn .primitive .primitive)))
    (.fn .primitive (.fn .primitive .primitive))

def get2nd : Trm :=
  .val
    (.fn (fun _x =>
      .val
        (.fn (fun y => .ref y))
        (.fn .primitive .primitive)))
    (.fn .primitive (.fn .primitive .primitive))

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
          (.ref x)))
        (.fn .primitive .primitive)))
    (.fn
      (.fn .primitive .primitive)
      (.fn .primitive .primitive))

def apply1stOn2ndFnOnTuple : Trm :=
  .apply
    (.apply apply1stOn2ndFn idFn)
    vFalse

def primitiveTrueFn : Trm :=
  .val
    (.fn (fun _x =>
      .val (.primitive "true") .primitive))
    (.fn .primitive .primitive)

def primitiveTrueFnOnFalse : Trm :=
  .apply primitiveTrueFn vFalse

namespace TypeHinted

def hintedFalse : Trm :=
  .val (.primitive "false") .primitive

def hintedIdFn : Trm :=
  .val
    (.fn (fun x => .ref x))
    (.fn .primitive .primitive)

def hintedIdFnOnFalse : Trm :=
  .apply hintedIdFn hintedFalse

end TypeHinted

namespace Malformed

def applyidFnOnItself : Trm :=
  .apply idFn idFn

def idFnOnFalse2 : Trm :=
  .apply applyidFnOnItself vFalse

def primitiveApply : Trm :=
  .apply vFalse vTrue

def apply1 : Trm :=
  .apply
    (.apply idFn vFalse)
    vTrue

def primitiveFalseAsFn : Trm :=
  .val
    (.primitive "false")
    (.fn .primitive .primitive)

def idFnAsPrimitive : Trm :=
  .val
    (.fn (fun x => .ref x))
    .primitive

end Malformed

end Trm

end Sanity
