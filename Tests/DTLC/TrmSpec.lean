import «Tests».DTLC.TrmDemo

namespace Tests.DTLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.DTLC
open Lp2lc.Active.DTLC.Symbolic
open Lp2lc.Active.DTLC.Runtime

section eraseType

example :
    (annotatedFalse : Trm).type.eraseRecursively =
      (false : Trm) := rfl

example :
    (annotatedIdFn : Trm).type.eraseRecursively =
      .val (.fn fun x => .ref x) none := rfl

example :
    (annotatedIdFnOnFalse : Trm).type.eraseRecursively =
      .apply
        (annotatedIdFn : Trm).type.eraseRecursively
        (false : Trm)
        none := rfl

end eraseType

section compile

example {I : Index} [Compiletime.Env I] :
    ((false : AST.Trm I).compile 0) = .outOfFuel := rfl

example {I : Index} [Compiletime.Env I] :
    ((false : AST.Trm I).compile 1) =
      .some ((false : AST.Trm I).type.eraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((true : AST.Trm I).compile 1) =
      .some ((true : AST.Trm I).type.eraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((idFn : AST.Trm I).compile 1) =
      .some ((idFn : AST.Trm I).type.eraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((idFnOnFalse : AST.Trm I).compile 2) =
      .some
        (.apply
          (idFn : AST.Trm I).type.eraseRecursively
          (false : AST.Trm I).type.eraseRecursively
          none) := rfl

example {I : Index} [Compiletime.Env I] :
    ((get1st : AST.Trm I).compile 1) =
      .some ((get1st : AST.Trm I).type.eraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((get2nd : AST.Trm I).compile 1) =
      .some ((get2nd : AST.Trm I).type.eraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((get1stOnTuple : AST.Trm I).compile 3) =
      .some ((get1stOnTuple : AST.Trm I).type.eraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((get2ndOnTuple : AST.Trm I).compile 3) =
      .some ((get2ndOnTuple : AST.Trm I).type.eraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((apply1stOn2ndFn : AST.Trm I).compile 1) =
      .some ((apply1stOn2ndFn : AST.Trm I).type.eraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((apply1stOn2ndFnOnTuple : AST.Trm I).compile 3) =
      .some ((apply1stOn2ndFnOnTuple : AST.Trm I).type.eraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((applyidFnOnItself : AST.Trm I).compile 2) =
      .some ((applyidFnOnItself : AST.Trm I).type.eraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((idFnOnFalse2 : AST.Trm I).compile 3) =
      .some ((idFnOnFalse2 : AST.Trm I).type.eraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((malformedApply1 : AST.Trm I).compile 4) =
      .error := rfl

example {I : Index} [Compiletime.Env I] :
    ((malformedPrimitiveApply : AST.Trm I).compile 2) = .error := rfl

example {I : Index} [Compiletime.Env I] :
    ((annotatedFalse : AST.Trm I).compile 1) =
      .some ((annotatedFalse : AST.Trm I).type.eraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((annotatedIdFn : AST.Trm I).compile 2) =
      .some ((annotatedIdFn : AST.Trm I).type.eraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((annotatedIdFnOnFalse : AST.Trm I).compile 3) =
      .some ((annotatedIdFnOnFalse : AST.Trm I).type.eraseRecursively) := rfl

example {I : Index} [Compiletime.Env I] :
    ((.val
      (.primitive "false")
      (some (.depFn .primitive (fun _ => .primitive))) : AST.Trm I).compile 1) =
      .error := rfl

example {I : Index} [Compiletime.Env I] :
    ((.val
      (.fn (fun x => .ref x))
      (some .primitive) : AST.Trm I).compile 1) =
      .error := rfl

end compile

section eval

@[reducible] unsafe def runtimeCanEval (value : Val) : Permission.Eval value :=
  unsafeCast ()

unsafe instance : Env Symbol where
  forVals := {
    save := fun value _permission => unsafeCast value
    load := fun ref => unsafeCast ref
    roundtrip := by
      intro value
      intro permission
      exact unsafeCast True.intro
  }
  canEvalAny := runtimeCanEval

unsafe example : ((Trm.false : Trm).eval 0) = .outOfFuel := by
  rfl

unsafe example : ((Trm.false : Trm).eval 1) =
    .some ((.primitive "false") : Val) := by
  rfl

unsafe example : ((Trm.false : Trm).eval 2) =
    .some ((.primitive "false") : Val) := by
  rfl

unsafe example : ((Trm.idFnOnFalse : Trm).eval 0) = .outOfFuel := by
  rfl

unsafe example : ((Trm.idFnOnFalse : Trm).eval 2) =
    .some ((.primitive "false") : Val) := by
  exact unsafeCast True.intro

unsafe example : ((Trm.get1stOnTuple : Trm).eval 1) = .outOfFuel := by
  rfl

unsafe example : ((Trm.get1stOnTuple : Trm).eval 3) =
    .some ((.primitive "false") : Val) := by
  exact unsafeCast True.intro

unsafe example : ((Trm.get2ndOnTuple : Trm).eval 3) =
    .some ((.primitive "true") : Val) := by
  exact unsafeCast True.intro

unsafe example : ((Trm.apply1stOn2ndFnOnTuple : Trm).eval 2) = .outOfFuel := by
  rfl

unsafe example : ((Trm.apply1stOn2ndFnOnTuple : Trm).eval 4) =
    .some ((.primitive "false") : Val) := by
  exact unsafeCast True.intro

unsafe example : ((Trm.applyidFnOnItself : Trm).eval 0) = .outOfFuel := by
  rfl

unsafe example : ((Trm.applyidFnOnItself : Trm).eval 2) =
    .some ((Val.idFn : Val)) := by
  exact unsafeCast True.intro

unsafe example : ((Trm.idFnOnFalse2 : Trm).eval 1) = .outOfFuel := by
  rfl

unsafe example : ((Trm.idFnOnFalse2 : Trm).eval 3) =
    .some ((.primitive "false") : Val) := by
  exact unsafeCast True.intro

unsafe example : ((Trm.malformedApply1 : Trm).eval 4) = .error := by
  exact unsafeCast True.intro

unsafe example : ((Trm.malformedPrimitiveApply : Trm).eval 0) = .outOfFuel := by
  rfl

unsafe example : ((Trm.malformedPrimitiveApply : Trm).eval 2) = .error := by
  rfl

unsafe example : ((Trm.malformedApply1 : Trm).eval 1) = .outOfFuel := by
  rfl

unsafe example : ((Trm.malformedApply1 : Trm).eval 3) = .error := by
  exact unsafeCast True.intro

end eval

end Trm

end Sanity
