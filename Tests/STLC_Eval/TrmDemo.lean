import «Tests».STLC_Eval.ValDemo

namespace Tests.STLC_Eval.Sanity

open Lp2lc.Active.Util
open Lp2lc.Active.STLC
open Tests.STLC_Eval.Sanity.Symbolic

namespace Trm

def vFalse : Trm :=
  .val Val.vFalse

def vTrue : Trm :=
  .val Val.vTrue

def primitiveIdFn : Trm :=
  .val Val.idFn

def primitiveIdFnOnFalse : Trm :=
  .apply primitiveIdFn vFalse

def primitiveTrueFn : Trm :=
  .val (.fn (fun _ref => vTrue) .primitive)

def primitiveTrueFnOnFalse : Trm :=
  .apply primitiveTrueFn vFalse

def get1st : Trm :=
  .val
    (.fn (fun firstRef =>
      .val (.fn (fun _secondRef => .ref firstRef) .primitive))
      .primitive)

def get1stOnTuple : Trm :=
  .apply (.apply get1st vFalse) vTrue

namespace Malformed

def primitiveApply : Trm :=
  .apply vFalse vTrue

def bodyFails : Trm :=
  .val (.fn (fun _ref => primitiveApply) .primitive)

def bodyFailsOnFalse : Trm :=
  .apply bodyFails vFalse

def idFnOnPrimitiveApply : Trm :=
  .apply primitiveIdFn primitiveApply

def primitiveApplyOnFalse : Trm :=
  .apply primitiveApply vFalse

end Malformed

end Trm

end Sanity
