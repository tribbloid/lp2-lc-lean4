import «Tests».DTLC.TrmDemo

namespace Tests.DTLC.Sanity
open Lp2lc.Active.Util
open Lp2lc.Active.DTLC

namespace Trm

section eraseType

example {I : Index} :
    (annotatedFalse : Trm I).typeEraseRecursively = (false : Trm I) := rfl

example {I : Index} :
    (annotatedIdFn : Trm I).typeEraseRecursively =
      .val (.fn (body := fun x => .ref x)) none := rfl

example {I : Index} :
    (annotatedIdFnOnFalse : Trm I).typeEraseRecursively =
      .apply (annotatedIdFn : Trm I).typeEraseRecursively (false : Trm I) none := rfl

end eraseType

section eval

unsafe inductive RuntimeRef where
| val (value : Val RuntimeRef) : RuntimeRef
| trm (term : Trm RuntimeRef) : RuntimeRef

unsafe instance : FBound RuntimeRef Val where
  save := RuntimeRef.val
  load := fun ref =>
    match ref with
    | .val value => value
    | .trm _ => .primitive "invalid-ref"
  roundtrip := by
    intro value
    rfl

unsafe instance : FBound RuntimeRef Trm where
  save := RuntimeRef.trm
  load := fun ref =>
    match ref with
    | .val _ => .val (.primitive "invalid-ref")
    | .trm trm => trm
  roundtrip := by
    intro trm
    rfl

unsafe example : ((Trm.false : Trm RuntimeRef).eval 0) = .outOfFuel := by
  rfl

unsafe example : ((Trm.false : Trm RuntimeRef).eval 1) =
    .some ((Val.primitive "false") : Val RuntimeRef) := by
  rfl

unsafe example : ((Trm.false : Trm RuntimeRef).eval 2) =
    .some ((Val.primitive "false") : Val RuntimeRef) := by
  rfl

unsafe example : ((Trm.idFnOnFalse : Trm RuntimeRef).eval 0) = .outOfFuel := by
  rfl

unsafe example : ((Trm.idFnOnFalse : Trm RuntimeRef).eval 2) =
    .some ((Val.primitive "false") : Val RuntimeRef) := by
  rfl

unsafe example : ((Trm.get1stOnTuple : Trm RuntimeRef).eval 1) = .outOfFuel := by
  rfl

unsafe example : ((Trm.get1stOnTuple : Trm RuntimeRef).eval 3) =
    .some ((Val.primitive "false") : Val RuntimeRef) := by
  rfl

unsafe example : ((Trm.get2ndOnTuple : Trm RuntimeRef).eval 3) =
    .some ((Val.primitive "true") : Val RuntimeRef) := by
  rfl

unsafe example : ((Trm.apply1stOn2ndFnOnTuple : Trm RuntimeRef).eval 2) = .outOfFuel := by
  rfl

unsafe example : ((Trm.apply1stOn2ndFnOnTuple : Trm RuntimeRef).eval 4) =
    .some ((Val.primitive "false") : Val RuntimeRef) := by
  rfl

unsafe example : ((Trm.applyidFnOnItself : Trm RuntimeRef).eval 0) = .outOfFuel := by
  rfl

unsafe example : ((Trm.applyidFnOnItself : Trm RuntimeRef).eval 2) =
    .some ((Val.idFn : Val RuntimeRef)) := by
  rfl

unsafe example : ((Trm.idFnOnFalse2 : Trm RuntimeRef).eval 1) = .outOfFuel := by
  rfl

unsafe example : ((Trm.idFnOnFalse2 : Trm RuntimeRef).eval 3) =
    .some ((Val.primitive "false") : Val RuntimeRef) := by
  rfl

unsafe example : ((Trm.malformedPrimitiveApply : Trm RuntimeRef).eval 0) = .outOfFuel := by
  rfl

unsafe example : ((Trm.malformedPrimitiveApply : Trm RuntimeRef).eval 2) = .error := by
  rfl

end eval

end Trm

end Sanity
