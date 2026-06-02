import «Tests».DTLC.TrmDemo

namespace Tests.DTLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.DTLC
open Lp2lc.Active.DTLC.Symbolic

section eraseType

example :
    TypeHinted.hintedFalse.typeHint.eraseRecursively =
      (false : Trm) := rfl

example :
    TypeHinted.hintedIdFn.typeHint.eraseRecursively =
      .val (.fn fun x => .ref x) := rfl

example :
    TypeHinted.hintedIdFnOnFalse.typeHint.eraseRecursively =
      .apply
        TypeHinted.hintedIdFn.typeHint.eraseRecursively
        (false : Trm) := rfl

end eraseType

section eval

@[reducible] unsafe def runtimeCanEval (value : Val) : Permission.Eval Val value :=
  unsafeCast ()

unsafe instance : Runtime.Env Symbol where
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

section compile

example [Compiletime.Env Symbol] :
    false.compile 0 = .outOfFuel := by
  sorry

example [Compiletime.Env Symbol] :
    false.compile 1 =
      .result false := by
  sorry

example [Compiletime.Env Symbol] :
    true.compile 1 =
      .result true := by
  sorry

example [Compiletime.Env Symbol] :
    idFn.compile 1 =
      .result idFn := by
  sorry

example [Compiletime.Env Symbol] :
    idFnOnFalse.compile 2 =
      .result idFnOnFalse := by
  sorry

example [Compiletime.Env Symbol] :
    get1st.compile 1 =
      .result get1st := by
  sorry

example [Compiletime.Env Symbol] :
    get2nd.compile 1 =
      .result get2nd := by
  sorry

example [Compiletime.Env Symbol] :
    get1stOnTuple.compile 3 =
      .result get1stOnTuple := by
  sorry

example [Compiletime.Env Symbol] :
    get2ndOnTuple.compile 3 =
      .result get2ndOnTuple := by
  sorry

example [Compiletime.Env Symbol] :
    apply1stOn2ndFn.compile 1 =
      .result apply1stOn2ndFn := by
  sorry

example [Compiletime.Env Symbol] :
    apply1stOn2ndFnOnTuple.compile 3 =
      .result apply1stOn2ndFnOnTuple := by
  sorry

example [Compiletime.Env Symbol] :
    applyidFnOnItself.compile 2 =
      .result applyidFnOnItself := by
  sorry

example [Compiletime.Env Symbol] :
    idFnOnFalse2.compile 3 =
      .result idFnOnFalse2 := by
  sorry


example [Compiletime.Env Symbol] :
    primitiveTrueFn.compile 1 =
      .result primitiveTrueFn := by
  sorry

example [Compiletime.Env Symbol] :
    primitiveTrueFnOnFalse.compile 2 =
      .result primitiveTrueFnOnFalse := by
  sorry

example [Compiletime.Env Symbol] :
    TypeHinted.hintedFalse.compile 2 =
      .result TypeHinted.hintedFalse.typeHint.eraseRecursively := by
  sorry

example [Compiletime.Env Symbol] :
    TypeHinted.hintedIdFn.compile 2 =
      .result TypeHinted.hintedIdFn.typeHint.eraseRecursively := by
  sorry

example [Compiletime.Env Symbol] :
    TypeHinted.hintedIdFnOnFalse.compile 4 =
      .result TypeHinted.hintedIdFnOnFalse.typeHint.eraseRecursively := by
  sorry

example [Compiletime.Env Symbol] :
    Malformed.apply1.compile 4 =
      .error := by
  sorry

example [Compiletime.Env Symbol] :
    Malformed.primitiveApply.compile 2 = .error := by
  sorry

example [Compiletime.Env Symbol] :
    Malformed.primitiveFalseAsFn.compile 2 =
      .error := by
  sorry

example [Compiletime.Env Symbol] :
    Malformed.idFnAsPrimitive.compile 2 =
      .error := by
  sorry

end compile

end Trm

end Sanity
