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

-- section compile

-- example {I : Index} [Compiletime.Env I] :
--     ((false : Trm I).compile 0) = .outOfFuel := rfl

-- example {I : Index} [Compiletime.Env I] :
--     ((false : Trm I).compile 1) =
--       .some ((false : Trm I).type.eraseRecursively) := rfl

-- example {I : Index} [Compiletime.Env I] :
--     ((true : Trm I).compile 1) =
--       .some ((true : Trm I).type.eraseRecursively) := rfl

-- example {I : Index} [Compiletime.Env I] :
--     ((idFn : Trm I).compile 1) =
--       .some ((idFn : Trm I).type.eraseRecursively) := rfl

-- example {I : Index} [Compiletime.Env I] :
--     ((idFnOnFalse : Trm I).compile 2) =
--       .some
--         (.apply
--           (idFn : Trm I).type.eraseRecursively
--           (false : Trm I).type.eraseRecursively
--           none) := rfl

-- example {I : Index} [Compiletime.Env I] :
--     ((get1st : Trm I).compile 1) =
--       .some ((get1st : Trm I).type.eraseRecursively) := rfl

-- example {I : Index} [Compiletime.Env I] :
--     ((get2nd : Trm I).compile 1) =
--       .some ((get2nd : Trm I).type.eraseRecursively) := rfl

-- example {I : Index} [Compiletime.Env I] :
--     ((get1stOnTuple : Trm I).compile 3) =
--       .some ((get1stOnTuple : Trm I).type.eraseRecursively) := rfl

-- example {I : Index} [Compiletime.Env I] :
--     ((get2ndOnTuple : Trm I).compile 3) =
--       .some ((get2ndOnTuple : Trm I).type.eraseRecursively) := rfl

-- example {I : Index} [Compiletime.Env I] :
--     ((apply1stOn2ndFn : Trm I).compile 1) =
--       .some ((apply1stOn2ndFn : Trm I).type.eraseRecursively) := rfl

-- example {I : Index} [Compiletime.Env I] :
--     ((apply1stOn2ndFnOnTuple : Trm I).compile 3) =
--       .some ((apply1stOn2ndFnOnTuple : Trm I).type.eraseRecursively) := rfl

-- example {I : Index} [Compiletime.Env I] :
--     ((applyidFnOnItself : Trm I).compile 2) =
--       .some ((applyidFnOnItself : Trm I).type.eraseRecursively) := rfl

-- example {I : Index} [Compiletime.Env I] :
--     ((idFnOnFalse2 : Trm I).compile 3) =
--       .some ((idFnOnFalse2 : Trm I).type.eraseRecursively) := rfl

-- example {I : Index} [Compiletime.Env I] :
--     ((malformedApply1 : Trm I).compile 4) =
--       .error := rfl

-- example {I : Index} [Compiletime.Env I] :
--     ((malformedPrimitiveApply : Trm I).compile 2) = .error := rfl

-- example {I : Index} [Compiletime.Env I] :
--     ((annotatedFalse : Trm I).compile 1) =
--       .some ((annotatedFalse : Trm I).type.eraseRecursively) := rfl

-- example {I : Index} [Compiletime.Env I] :
--     ((annotatedIdFn : Trm I).compile 2) =
--       .some ((annotatedIdFn : Trm I).type.eraseRecursively) := rfl

-- example {I : Index} [Compiletime.Env I] :
--     ((annotatedIdFnOnFalse : Trm I).compile 3) =
--       .some ((annotatedIdFnOnFalse : Trm I).type.eraseRecursively) := rfl

-- example {I : Index} [Compiletime.Env I] :
--     ((.val
--       (.primitive "false")
--       (some (.depFn .primitive (fun _ => .primitive))) : Trm I).compile 1) =
--       .error := rfl

-- example {I : Index} [Compiletime.Env I] :
--     ((.val
--       (.fn (fun x => .ref x))
--       (some .primitive) : Trm I).compile 1) =
--       .error := rfl

-- end compile

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
