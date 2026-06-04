import «Tests».DTLC.TrmDemo

namespace Tests.DTLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.DTLC
open Lp2lc.Active.DTLC.Symbolic

section eraseType

example :
    TypeHinted.hintedFalse.typeHint.eraseRecursively =
      (vFalse : Trm) := rfl

example :
    TypeHinted.hintedIdFn.typeHint.eraseRecursively =
      .val (.fn fun x => .ref x) := rfl

example :
    TypeHinted.hintedIdFnOnFalse.typeHint.eraseRecursively =
      .apply
        TypeHinted.hintedIdFn.typeHint.eraseRecursively
        (vFalse : Trm) := rfl

end eraseType

section eval

@[reducible] def RuntimeCanEval : Permission Val := fun _value => True

unsafe instance : Runtime.Env impl where
  EvalPermission := RuntimeCanEval
  forVals := {
    save := fun value _permission => unsafeCast value
    load := fun ref => unsafeCast ref
    roundtrip := by
      intro value
      intro permission
      exact unsafeCast True.intro
  }
  canEvalAny := fun _value => True.intro

unsafe example : ((Trm.vFalse : Trm).eval 0) = .outOfFuel := by
  rfl

unsafe example : ((Trm.vFalse : Trm).eval 1) =
    .result ((.primitive "false") : Val) := by
  rfl

unsafe example : ((Trm.vFalse : Trm).eval 2) =
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

section compile

unsafe instance : Compiletime.Env impl where
  forTyps := {
    save := fun typ _permission => unsafeCast typ
    load := fun ref => unsafeCast ref
    roundtrip := by
      intro typ
      intro permission
      exact unsafeCast True.intro
  }

example :
    vFalse.compile.isSemiDecidable := by
  sorry

example :
    vFalse.compile.isSemiDecidable := by
  sorry

example :
    vTrue.compile.isSemiDecidable := by
  sorry

example :
    idFn.compile.isSemiDecidable := by
  sorry

example :
    idFnOnFalse.compile.isSemiDecidable := by
  sorry

example :
    get1st.compile.isSemiDecidable := by
  sorry

example :
    get2nd.compile.isSemiDecidable := by
  sorry

example :
    get1stOnTuple.compile.isSemiDecidable := by
  sorry

example :
    get2ndOnTuple.compile.isSemiDecidable := by
  sorry

example :
    apply1stOn2ndFn.compile.isSemiDecidable := by
  sorry

example :
    apply1stOn2ndFnOnTuple.compile.isSemiDecidable := by
  sorry

example :
    applyidFnOnItself.compile.isSemiDecidable := by
  sorry

example :
    idFnOnFalse2.compile.isSemiDecidable := by
  sorry


example :
    primitiveTrueFn.compile.isSemiDecidable := by
  sorry

example :
    primitiveTrueFnOnFalse.compile.isSemiDecidable := by
  sorry

example :
    TypeHinted.hintedFalse.compile.isSemiDecidable := by
  sorry

example :
    TypeHinted.hintedIdFn.compile.isSemiDecidable := by
  sorry

example :
    TypeHinted.hintedIdFnOnFalse.compile.isSemiDecidable := by
  sorry

example :
    Malformed.apply1.compile 4 =
      .error := by
  sorry

example :
    Malformed.primitiveApply.compile 2 = .error := by
  sorry

example :
    Malformed.primitiveFalseAsFn.compile 2 =
      .error := by
  sorry

example :
    Malformed.idFnAsPrimitive.compile 2 =
      .error := by
  sorry

end compile

end Trm

end Sanity
