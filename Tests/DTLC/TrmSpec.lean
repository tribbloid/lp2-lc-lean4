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
      .val (.fn fun x => .ref x) none := rfl

example {I : Index} :
    (annotatedIdFnOnFalse : Trm I).typeEraseRecursively =
      .apply (annotatedIdFn : Trm I).typeEraseRecursively (false : Trm I) none := rfl

end eraseType

section compile

example {I : Index} [Compiletime.Env I] :
    ((false : Trm I).compile 0) = .outOfFuel := rfl

example {I : Index} [Compiletime.Env I] :
    ((false : Trm I).compile 1) =
      .some ((false : Trm I).typeEraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((true : Trm I).compile 1) =
      .some ((true : Trm I).typeEraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((idFn : Trm I).compile 1) =
      .some ((idFn : Trm I).typeEraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((idFnOnFalse : Trm I).compile 2) =
      .some
        (.apply
          (idFn : Trm I).typeEraseRecursively
          (false : Trm I).typeEraseRecursively
          none) := rfl

example {I : Index} [Compiletime.Env I] :
    ((get1st : Trm I).compile 1) =
      .some ((get1st : Trm I).typeEraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((get2nd : Trm I).compile 1) =
      .some ((get2nd : Trm I).typeEraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((get1stOnTuple : Trm I).compile 3) =
      .some ((get1stOnTuple : Trm I).typeEraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((get2ndOnTuple : Trm I).compile 3) =
      .some ((get2ndOnTuple : Trm I).typeEraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((apply1stOn2ndFn : Trm I).compile 1) =
      .some ((apply1stOn2ndFn : Trm I).typeEraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((apply1stOn2ndFnOnTuple : Trm I).compile 3) =
      .some ((apply1stOn2ndFnOnTuple : Trm I).typeEraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((applyidFnOnItself : Trm I).compile 2) =
      .some ((applyidFnOnItself : Trm I).typeEraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((idFnOnFalse2 : Trm I).compile 3) =
      .some ((idFnOnFalse2 : Trm I).typeEraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((malformedApply1 : Trm I).compile 4) =
      .error := rfl

example {I : Index} [Compiletime.Env I] :
    ((malformedPrimitiveApply : Trm I).compile 2) = .error := rfl

example {I : Index} [Compiletime.Env I] :
    ((annotatedFalse : Trm I).compile 1) =
      .some ((annotatedFalse : Trm I).typeEraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((annotatedIdFn : Trm I).compile 2) =
      .some ((annotatedIdFn : Trm I).typeEraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((annotatedIdFnOnFalse : Trm I).compile 3) =
      .some ((annotatedIdFnOnFalse : Trm I).typeEraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((.val
      (.primitive "false")
      (some (.depFn .primitive (fun _ => .primitive))) : Trm I).compile 1) =
      .error := rfl

example {I : Index} [Compiletime.Env I] :
    ((.val
      (.fn (fun x => .ref x))
      (some .primitive) : Trm I).compile 1) =
      .error := rfl

end compile

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

unsafe instance : Env RuntimeRef where
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

unsafe example : ((Trm.malformedApply1 : Trm RuntimeRef).eval 4) = .error := by
  rfl

unsafe example : ((Trm.malformedPrimitiveApply : Trm RuntimeRef).eval 0) = .outOfFuel := by
  rfl

unsafe example : ((Trm.malformedPrimitiveApply : Trm RuntimeRef).eval 2) = .error := by
  rfl

end eval

end Trm

end Sanity
