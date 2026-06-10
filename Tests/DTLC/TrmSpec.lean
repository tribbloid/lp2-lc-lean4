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
    vFalse.compileToTrm.shouldYields vFalse := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    vTrue.compileToTrm.shouldYields vTrue := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    idFn.compileToTrm.shouldYields idFn := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    idFnOnFalse.compileToTrm.shouldFail := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    get1st.compileToTrm.shouldYields get1st := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    get2nd.compileToTrm.shouldYields get2nd := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    get1stOnTuple.compileToTrm.shouldFail := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    get2ndOnTuple.compileToTrm.shouldFail := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    apply1stOn2ndFn.compileToTrm.shouldYields apply1stOn2ndFn := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    apply1stOn2ndFnOnTuple.compileToTrm.shouldFail := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    applyidFnOnItself.compileToTrm.shouldFail := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    idFnOnFalse2.compileToTrm.shouldFail := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl


example :
    primitiveTrueFn.compileToTrm.shouldYields primitiveTrueFn := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    primitiveTrueFnOnFalse.compileToTrm.shouldYields
      primitiveTrueFnOnFalse := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

example :
    TypeHinted.hintedFalse.compileToTrm.shouldYields
      TypeHinted.hintedFalse.typeHint.eraseRecursively := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

example :
    TypeHinted.hintedIdFn.compileToTrm.shouldYields
      TypeHinted.hintedIdFn.typeHint.eraseRecursively := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

example :
    TypeHinted.hintedIdFnOnFalse.compileToTrm.shouldFail := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

example :
    Malformed.apply1.compileToTrm.shouldFail := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    Malformed.primitiveApply.compileToTrm.shouldFail := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    Malformed.primitiveFalseAsFn.compileToTrm.shouldFail := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

example :
    Malformed.idFnAsPrimitive.compileToTrm.shouldFail := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

end compile

end Trm

end Sanity
