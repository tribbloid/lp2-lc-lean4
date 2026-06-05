import «Tests».DTLC.Fixture

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

example :
    ((Trm.vFalse : Trm).eval).yields
      ((.primitive "false") : Val) := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    ((Trm.idFnOnFalse : Trm).eval).yields
      ((.primitive "false") : Val) := by
  constructor
  · exact ⟨2, by simp [AST.Trm.eval, idFnOnFalse, idFn, vFalse]⟩
  · rfl

example :
    ((Trm.get1stOnTuple : Trm).eval).yields
      ((.primitive "false") : Val) := by
  constructor
  · exact ⟨3, by simp [AST.Trm.eval, get1stOnTuple, get1st, vFalse, vTrue]⟩
  · rfl

example :
    ((Trm.get2ndOnTuple : Trm).eval).yields
      ((.primitive "true") : Val) := by
  constructor
  · exact ⟨3, by simp [AST.Trm.eval, get2ndOnTuple, get2nd, vFalse, vTrue]⟩
  · rfl

example :
    ((Trm.apply1stOn2ndFnOnTuple : Trm).eval).yields
      ((.primitive "false") : Val) := by
  constructor
  · exact ⟨4, by simp [AST.Trm.eval, apply1stOn2ndFnOnTuple, apply1stOn2ndFn, idFn, vFalse]⟩
  · rfl

example :
    ((Trm.applyidFnOnItself : Trm).eval).yields
      (Val.idFn : Val) := by
  constructor
  · exact ⟨2, by simp [AST.Trm.eval, applyidFnOnItself, idFn, Val.idFn]⟩
  · rfl

example :
    ((Trm.idFnOnFalse2 : Trm).eval).yields
      ((.primitive "false") : Val) := by
  constructor
  · exact ⟨3, by simp [AST.Trm.eval, idFnOnFalse2, applyidFnOnItself, idFn, vFalse]⟩
  · rfl

example: ((Trm.Malformed.apply1 : Trm).eval 4) = .error := by
  simp [AST.Trm.eval, Malformed.apply1, idFn, vFalse, vTrue]

example: ((Trm.Malformed.primitiveApply : Trm).eval 2) = .error := by
  rfl

example: ((Trm.Malformed.apply1 : Trm).eval 3) = .error := by
  simp [AST.Trm.eval, Malformed.apply1, idFn, vFalse, vTrue]

example :
    ((Trm.primitiveTrueFnOnFalse : Trm).eval).yields
      ((.primitive "true") : Val) := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

end eval

section compile

example :
    vFalse.compile.yields vFalse := by
  sorry

example :
    vTrue.compile.yields vTrue := by
  sorry

example :
    idFn.compile.yields idFn := by
  sorry

example :
    idFnOnFalse.compile.yields idFnOnFalse := by
  sorry

example :
    get1st.compile.yields get1st := by
  sorry

example :
    get2nd.compile.yields get2nd := by
  sorry

example :
    get1stOnTuple.compile.yields get1stOnTuple := by
  sorry

example :
    get2ndOnTuple.compile.yields get2ndOnTuple := by
  sorry

example :
    apply1stOn2ndFn.compile.yields apply1stOn2ndFn := by
  sorry

example :
    apply1stOn2ndFnOnTuple.compile.yields
      apply1stOn2ndFnOnTuple := by
  sorry

example :
    applyidFnOnItself.compile.yields applyidFnOnItself := by
  sorry

example :
    idFnOnFalse2.compile.yields idFnOnFalse2 := by
  sorry


example :
    primitiveTrueFn.compile.yields primitiveTrueFn := by
  sorry

example :
    primitiveTrueFnOnFalse.compile.yields
      primitiveTrueFnOnFalse := by
  sorry

example :
    TypeHinted.hintedFalse.compile.yields
      TypeHinted.hintedFalse.typeHint.eraseRecursively := by
  sorry

example :
    TypeHinted.hintedIdFn.compile.yields
      TypeHinted.hintedIdFn.typeHint.eraseRecursively := by
  sorry

example :
    TypeHinted.hintedIdFnOnFalse.compile.yields
      TypeHinted.hintedIdFnOnFalse.typeHint.eraseRecursively := by
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
