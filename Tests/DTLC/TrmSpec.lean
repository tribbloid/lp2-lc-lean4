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
      .val (.fn fun x => .ref x) := rfl

example :
    (annotatedIdFnOnFalse : Trm).type.eraseRecursively =
      .apply
        (annotatedIdFn : Trm).type.eraseRecursively
        (false : Trm) := rfl

end eraseType

section compile

example [Compiletime.Env Symbol] :
    ((false : Trm).compile 0) = .outOfFuel := rfl

example [Compiletime.Env Symbol] :
    ((false : Trm).compile 1) =
      .result ((false : Trm).type.eraseRecursively) := rfl

example [Compiletime.Env Symbol] :
    ((true : Trm).compile 1) =
      .result ((true : Trm).type.eraseRecursively) := rfl

example [Compiletime.Env Symbol] :
    ((idFn : Trm).compile 1) =
      .result ((idFn : Trm).type.eraseRecursively) := rfl

example [Compiletime.Env Symbol] :
    ((idFnOnFalse : Trm).compile 2) =
      .result
        (.apply
          (idFn : Trm).type.eraseRecursively
          (false : Trm).type.eraseRecursively) := rfl

example [Compiletime.Env Symbol] :
    ((get1st : Trm).compile 1) =
      .result ((get1st : Trm).type.eraseRecursively) := rfl

example [Compiletime.Env Symbol] :
    ((get2nd : Trm).compile 1) =
      .result ((get2nd : Trm).type.eraseRecursively) := rfl

example [Compiletime.Env Symbol] :
    ((get1stOnTuple : Trm).compile 3) =
      .result ((get1stOnTuple : Trm).type.eraseRecursively) := rfl

example [Compiletime.Env Symbol] :
    ((get2ndOnTuple : Trm).compile 3) =
      .result ((get2ndOnTuple : Trm).type.eraseRecursively) := rfl

example [Compiletime.Env Symbol] :
    ((apply1stOn2ndFn : Trm).compile 1) =
      .result ((apply1stOn2ndFn : Trm).type.eraseRecursively) := rfl

example [Compiletime.Env Symbol] :
    ((apply1stOn2ndFnOnTuple : Trm).compile 3) =
      .result ((apply1stOn2ndFnOnTuple : Trm).type.eraseRecursively) := rfl

example [Compiletime.Env Symbol] :
    ((applyidFnOnItself : Trm).compile 2) =
      .result ((applyidFnOnItself : Trm).type.eraseRecursively) := rfl

example [Compiletime.Env Symbol] :
    ((idFnOnFalse2 : Trm).compile 3) =
      .result ((idFnOnFalse2 : Trm).type.eraseRecursively) := rfl

example [Compiletime.Env Symbol] :
    ((Malformed.apply1 : Trm).compile 4) =
      .error := rfl

example [Compiletime.Env Symbol] :
    ((Malformed.primitiveApply : Trm).compile 2) = .error := rfl

example [Compiletime.Env Symbol] :
    ((primitiveTrueFn : Trm).compile 1) =
      .result ((primitiveTrueFn : Trm).type.eraseRecursively) := rfl

example [Compiletime.Env Symbol] :
    ((primitiveTrueFnOnFalse : Trm).compile 2) =
      .result ((primitiveTrueFnOnFalse : Trm).type.eraseRecursively) := rfl

example [Compiletime.Env Symbol] :
    ((annotatedFalse : Trm).compile 2) =
      .result ((annotatedFalse : Trm).type.eraseRecursively) := rfl

example [Compiletime.Env Symbol] :
    ((annotatedIdFn : Trm).compile 2) =
      .result ((annotatedIdFn : Trm).type.eraseRecursively) := rfl

example [Compiletime.Env Symbol] :
    ((annotatedIdFnOnFalse : Trm).compile 4) =
      .result ((annotatedIdFnOnFalse : Trm).type.eraseRecursively) := rfl

example [Compiletime.Env Symbol] :
    ((.typeHinted
      (.val (.primitive "false"))
      (.depFn .primitive (fun _ => .primitive)) : Trm).compile 2) =
      .error := rfl

example [Compiletime.Env Symbol] :
    ((.typeHinted
      (.val (.fn (fun x => .ref x)))
      .primitive : Trm).compile 2) =
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
    .result ((.primitive "false") : Val) := by
  rfl

unsafe example : ((Trm.false : Trm).eval 2) =
    .result ((.primitive "false") : Val) := by
  rfl

unsafe example : ((Trm.idFnOnFalse : Trm).eval 0) = .outOfFuel := by
  rfl

unsafe example : ((Trm.idFnOnFalse : Trm).eval 2) =
    .result ((.primitive "false") : Val) := by
  exact unsafeCast True.intro

unsafe example : ((Trm.get1stOnTuple : Trm).eval 1) = .outOfFuel := by
  rfl

unsafe example : ((Trm.get1stOnTuple : Trm).eval 3) =
    .result ((.primitive "false") : Val) := by
  exact unsafeCast True.intro

unsafe example : ((Trm.get2ndOnTuple : Trm).eval 3) =
    .result ((.primitive "true") : Val) := by
  exact unsafeCast True.intro

unsafe example : ((Trm.apply1stOn2ndFnOnTuple : Trm).eval 2) = .outOfFuel := by
  rfl

unsafe example : ((Trm.apply1stOn2ndFnOnTuple : Trm).eval 4) =
    .result ((.primitive "false") : Val) := by
  exact unsafeCast True.intro

unsafe example : ((Trm.applyidFnOnItself : Trm).eval 0) = .outOfFuel := by
  rfl

unsafe example : ((Trm.applyidFnOnItself : Trm).eval 2) =
    .result ((Val.idFn : Val)) := by
  exact unsafeCast True.intro

unsafe example : ((Trm.idFnOnFalse2 : Trm).eval 1) = .outOfFuel := by
  rfl

unsafe example : ((Trm.idFnOnFalse2 : Trm).eval 3) =
    .result ((.primitive "false") : Val) := by
  exact unsafeCast True.intro

unsafe example : ((Trm.Malformed.apply1 : Trm).eval 4) = .error := by
  exact unsafeCast True.intro

unsafe example : ((Trm.Malformed.primitiveApply : Trm).eval 0) = .outOfFuel := by
  rfl

unsafe example : ((Trm.Malformed.primitiveApply : Trm).eval 2) = .error := by
  rfl

unsafe example : ((Trm.Malformed.apply1 : Trm).eval 1) = .outOfFuel := by
  rfl

unsafe example : ((Trm.Malformed.apply1 : Trm).eval 3) = .error := by
  exact unsafeCast True.intro

unsafe example : ((Trm.primitiveTrueFnOnFalse : Trm).eval 2) =
    .result ((.primitive "true") : Val) := by
  rfl

end eval

end Trm

end Sanity
