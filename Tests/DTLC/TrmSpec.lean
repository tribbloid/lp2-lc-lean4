import «Tests».DTLC.TrmDemo

namespace Tests.DTLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.DTLC
open Lp2lc.Active.DTLC.AST
open Lp2lc.Active.DTLC.Runtime

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

@[reducible] unsafe def runtimeCanEval (value : Val RuntimeRef) : Permission.Eval value :=
  unsafeCast ()

unsafe instance : FBound RuntimeRef Val Permission.Eval where
  save := fun value _permission => RuntimeRef.val value
  load := fun ref =>
    match ref with
    | .val value => value
  roundtrip := by
    intro value
    intro permission
    rfl

unsafe instance : EvalEnv RuntimeRef where
  forVals := inferInstance
  canEvalAny := runtimeCanEval

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
