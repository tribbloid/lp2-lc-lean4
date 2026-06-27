import «Tests».STLC.Fixture

namespace Tests.STLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

section eval
variable [env : @RuntimeEnv Symbolic.I]

example :
    ((Trm.vFalse : Trm).eval).shouldYields
      ((.primitive "false") : Val) := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    ((Trm.primitiveIdFnOnFalse : Trm).eval).shouldYields
      ((.primitive "false") : Val) := by
  constructor
  · exact ⟨2, by simp [AST.Trm.eval, primitiveIdFnOnFalse, primitiveIdFn, vFalse]⟩
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
    ((Trm.Malformed.applyidFnOnItself : Trm).eval).shouldYields
      (Val.idFn : Val) := by
  constructor
  · exact ⟨2, by simp [AST.Trm.eval, Malformed.applyidFnOnItself, primitiveIdFn, Val.idFn]⟩
  · rfl

example :
    ((Trm.Malformed.idFnOnFalse2 : Trm).eval).shouldYields
      ((.primitive "false") : Val) := by
  constructor
  · exact ⟨3, by simp [AST.Trm.eval, Malformed.idFnOnFalse2, Malformed.applyidFnOnItself, primitiveIdFn, vFalse]⟩
  · rfl

example :
    ((Trm.Malformed.apply1 : Trm).eval).shouldFail := by
  constructor
  · exact ⟨4, by simp [AST.Trm.eval, Malformed.apply1, primitiveIdFn, vFalse, vTrue]⟩
  · rfl

example :
    ((Trm.Malformed.primitiveApply : Trm).eval).shouldFail := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

example :
    ((Trm.primitiveTrueFnOnFalse : Trm).eval).shouldYields
      ((.primitive "true") : Val) := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

end eval

section compile
variable [env : @CompilerEnv Symbolic.I]

example :
    (vFalse.recCanInhabit .primitive).shouldYields () := by
  sorry

example :
    (vTrue.recCanInhabit .primitive).shouldYields () := by
  sorry

example :
    (primitiveIdFn.recCanInhabit (.fn .primitive .primitive)).shouldYields () := by
  sorry

example :
    (primitiveIdFnOnFalse.recCanInhabit .primitive).shouldYields () := by
  sorry

example :
    (get1st.recCanInhabit (.fn .primitive (.fn .primitive .primitive))).shouldYields () := by
  sorry

example :
    (get2nd.recCanInhabit (.fn .primitive (.fn .primitive .primitive))).shouldYields () := by
  sorry

example :
    (get1stOnTuple.recCanInhabit .primitive).shouldYields () := by
  sorry

example :
    (get2ndOnTuple.recCanInhabit .primitive).shouldYields () := by
  sorry

example :
    (primitiveTrueFn.recCanInhabit (.fn .primitive .primitive)).shouldYields () := by
  sorry

example :
    (primitiveTrueFnOnFalse.recCanInhabit .primitive).shouldYields () := by
  sorry

example :
    (TypeHinted.hintedFalse.recCanInhabit .primitive).shouldYields () := by
  sorry

example :
    (TypeHinted.hintedIdFn.recCanInhabit (.fn .primitive .primitive)).shouldYields () := by
  sorry

example :
    (TypeHinted.hintedIdFnOnFalse.recCanInhabit .primitive).shouldYields () := by
  sorry

example :
    ∀ typ, (Malformed.applyidFnOnItself.recCanInhabit typ).shouldFail := by
  sorry

example :
    ∀ typ, (Malformed.idFnOnFalse2.recCanInhabit typ).shouldFail := by
  sorry

example :
    ∀ typ, (Malformed.apply1.recCanInhabit typ).shouldFail := by
  sorry

example :
    ∀ typ, (Malformed.primitiveApply.recCanInhabit typ).shouldFail := by
  sorry

end compile

end Trm

end Sanity
