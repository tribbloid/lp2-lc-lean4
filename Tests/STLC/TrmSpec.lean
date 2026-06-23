import «Tests».STLC.Fixture

namespace Tests.STLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

section typeHint

example :
    TypeHinted.hintedFalse.typeHint.get =
      some (.primitive : Typ) := rfl

example :
    TypeHinted.hintedIdFn.typeHint.get =
      some (.fn .primitive .primitive : Typ) := rfl

example :
    TypeHinted.hintedIdFnOnFalse.typeHint.get =
      (none : Option Typ) := rfl

end typeHint

section eval
variable [env : @Runtime.Env Symbolic.I]

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
variable [env : Compiler.Env Symbolic.I]

example :
    vFalse.CanInhabit .primitive := by
  sorry

example :
    vTrue.CanInhabit .primitive := by
  sorry

example :
    primitiveIdFn.CanInhabit (.fn .primitive .primitive) := by
  sorry

example :
    primitiveIdFnOnFalse.CanInhabit .primitive := by
  sorry

example :
    get1st.CanInhabit (.fn .primitive (.fn .primitive .primitive)) := by
  sorry

example :
    get2nd.CanInhabit (.fn .primitive (.fn .primitive .primitive)) := by
  sorry

example :
    get1stOnTuple.CanInhabit .primitive := by
  sorry

example :
    get2ndOnTuple.CanInhabit .primitive := by
  sorry

example :
    primitiveTrueFn.CanInhabit (.fn .primitive .primitive) := by
  sorry

example :
    primitiveTrueFnOnFalse.CanInhabit .primitive := by
  sorry

example :
    TypeHinted.hintedFalse.CanInhabit .primitive := by
  sorry

example :
    TypeHinted.hintedIdFn.CanInhabit (.fn .primitive .primitive) := by
  sorry

example :
    TypeHinted.hintedIdFnOnFalse.CanInhabit .primitive := by
  sorry

example :
    ¬ ∃ typ, Malformed.applyidFnOnItself.CanInhabit typ := by
  sorry

example :
    ¬ ∃ typ, Malformed.idFnOnFalse2.CanInhabit typ := by
  sorry

example :
    ¬ ∃ typ, Malformed.apply1.CanInhabit typ := by
  sorry

example :
    ¬ ∃ typ, Malformed.primitiveApply.CanInhabit typ := by
  sorry

example :
    ¬ ∃ typ, Malformed.primitiveFalseAsFn.CanInhabit typ := by
  sorry

example :
    ¬ ∃ typ, Malformed.idFnAsPrimitive.CanInhabit typ := by
  sorry

end compile

end Trm

end Sanity
