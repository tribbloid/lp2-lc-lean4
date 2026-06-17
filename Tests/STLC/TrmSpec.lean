import «Tests».STLC.Fixture

namespace Tests.STLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

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
    ((Trm.vFalse : Trm).eval).shouldYields
      ((.primitive "false") : Val) := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    ((Trm.idFnOnFalse : Trm).eval).shouldYields
      ((.primitive "false") : Val) := by
  constructor
  · exact ⟨2, by simp [AST.Trm.eval, idFnOnFalse, idFn, vFalse]⟩
  · rfl

example :
    ((Trm.get1stOnTuple : Trm).eval).shouldYields
      ((.primitive "false") : Val) := by
  constructor
  · exact ⟨3, by simp [AST.Trm.eval, get1stOnTuple, get1st, vFalse, vTrue]⟩
  · rfl

example :
    ((Trm.get2ndOnTuple : Trm).eval).shouldYields
      ((.primitive "true") : Val) := by
  constructor
  · exact ⟨3, by simp [AST.Trm.eval, get2ndOnTuple, get2nd, vFalse, vTrue]⟩
  · rfl

example :
    ((Trm.apply1stOn2ndFnOnTuple : Trm).eval).shouldYields
      ((.primitive "false") : Val) := by
  constructor
  · exact ⟨4, by simp [AST.Trm.eval, apply1stOn2ndFnOnTuple, apply1stOn2ndFn, idFn, vFalse]⟩
  · rfl

example :
    ((Trm.applyidFnOnItself : Trm).eval).shouldYields
      (Val.idFn : Val) := by
  constructor
  · exact ⟨2, by simp [AST.Trm.eval, applyidFnOnItself, idFn, Val.idFn]⟩
  · rfl

example :
    ((Trm.idFnOnFalse2 : Trm).eval).shouldYields
      ((.primitive "false") : Val) := by
  constructor
  · exact ⟨3, by simp [AST.Trm.eval, idFnOnFalse2, applyidFnOnItself, idFn, vFalse]⟩
  · rfl

example :
    ((Trm.Malformed.apply1 : Trm).eval).shouldFail := by
  constructor
  · exact ⟨4, by simp [AST.Trm.eval, Malformed.apply1, idFn, vFalse, vTrue]⟩
  · rfl

example :
    ((Trm.Malformed.primitiveApply : Trm).eval).shouldFail := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

example :
    ((Trm.Malformed.apply1 : Trm).eval).shouldFail := by
  constructor
  · exact ⟨3, by simp [AST.Trm.eval, Malformed.apply1, idFn, vFalse, vTrue]⟩
  · rfl

example :
    ((Trm.primitiveTrueFnOnFalse : Trm).eval).shouldYields
      ((.primitive "true") : Val) := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

end eval

section compile

example :
    vFalse.compile.isDecidable := by
  sorry

example :
    vTrue.compile.isDecidable := by
  sorry

example :
    idFn.compile.isDecidable := by
  sorry

example :
    idFnOnFalse.compile.isDecidable := by
  sorry

example :
    get1st.compile.isDecidable := by
  sorry

example :
    get2nd.compile.isDecidable := by
  sorry

example :
    get1stOnTuple.compile.isDecidable := by
  sorry

example :
    get2ndOnTuple.compile.isDecidable := by
  sorry

example :
    apply1stOn2ndFn.compile.isDecidable := by
  sorry

example :
    apply1stOn2ndFnOnTuple.compile.isDecidable := by
  sorry

example :
    applyidFnOnItself.compile.isDecidable := by
  sorry

example :
    idFnOnFalse2.compile.isDecidable := by
  sorry


example :
    primitiveTrueFn.compile.isDecidable := by
  sorry

example :
    primitiveTrueFnOnFalse.compile.isDecidable := by
  sorry

example :
    TypeHinted.hintedFalse.compile.isDecidable := by
  sorry

example :
    TypeHinted.hintedIdFn.compile.isDecidable := by
  sorry

example :
    TypeHinted.hintedIdFnOnFalse.compile.isDecidable := by
  sorry

example :
    Malformed.apply1.compile.shouldFail := by
  sorry

example :
    Malformed.primitiveApply.compile.shouldFail := by
  sorry

example :
    Malformed.primitiveFalseAsFn.compile.shouldFail := by
  sorry

example :
    Malformed.idFnAsPrimitive.compile.shouldFail := by
  sorry

end compile

end Trm

end Sanity
