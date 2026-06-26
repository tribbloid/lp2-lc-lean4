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
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    (vTrue.recCanInhabit .primitive).shouldYields () := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    (primitiveIdFn.recCanInhabit (.fn .primitive .primitive)).shouldYields () := by
  constructor
  · exact ⟨2, by
      simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map, primitiveIdFn]
      have h : (AST.Typ.primitive.fn AST.Typ.primitive : AST.Typ I) ≤ (AST.Typ.primitive.fn AST.Typ.primitive : AST.Typ I) := rfl
      simp [h]⟩
  · simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map]

example :
    (primitiveIdFnOnFalse.recCanInhabit .primitive).shouldYields () := by
  constructor
  · exact ⟨3, by
      simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map, primitiveIdFnOnFalse, primitiveIdFn, vFalse]
      have h : (AST.Typ.primitive : AST.Typ I) ≤ (AST.Typ.primitive : AST.Typ I) := rfl
      simp [h]⟩
  · simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map]

example :
    (get1st.recCanInhabit (.fn .primitive (.fn .primitive .primitive))).shouldYields () := by
  constructor
  · exact ⟨3, by
      simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map, get1st]
      have h : (AST.Typ.primitive.fn (AST.Typ.primitive.fn AST.Typ.primitive) : AST.Typ I) ≤
               (AST.Typ.primitive.fn (AST.Typ.primitive.fn AST.Typ.primitive) : AST.Typ I) := rfl
      simp [h]⟩
  · simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map]

example :
    (get2nd.recCanInhabit (.fn .primitive (.fn .primitive .primitive))).shouldYields () := by
  constructor
  · exact ⟨3, by
      simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map, get2nd]
      have h : (AST.Typ.primitive.fn (AST.Typ.primitive.fn AST.Typ.primitive) : AST.Typ I) ≤
               (AST.Typ.primitive.fn (AST.Typ.primitive.fn AST.Typ.primitive) : AST.Typ I) := rfl
      simp [h]⟩
  · simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map]

example :
    (get1stOnTuple.recCanInhabit .primitive).shouldYields () := by
  constructor
  · exact ⟨5, by
      simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map, get1stOnTuple, get1st, vFalse, vTrue]
      have h : (AST.Typ.primitive : AST.Typ I) ≤ (AST.Typ.primitive : AST.Typ I) := rfl
      simp [h]⟩
  · simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map]

example :
    (get2ndOnTuple.recCanInhabit .primitive).shouldYields () := by
  constructor
  · exact ⟨5, by
      simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map, get2ndOnTuple, get2nd, vFalse, vTrue]
      have h : (AST.Typ.primitive : AST.Typ I) ≤ (AST.Typ.primitive : AST.Typ I) := rfl
      simp [h]⟩
  · simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map]

example :
    (primitiveTrueFn.recCanInhabit (.fn .primitive .primitive)).shouldYields () := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

example :
    (primitiveTrueFnOnFalse.recCanInhabit .primitive).shouldYields () := by
  constructor
  · exact ⟨3, rfl⟩
  · rfl

example :
    (TypeHinted.hintedFalse.recCanInhabit .primitive).shouldYields () := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    (TypeHinted.hintedIdFn.recCanInhabit (.fn .primitive .primitive)).shouldYields () := by
  constructor
  · exact ⟨2, by
      simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map, TypeHinted.hintedIdFn]
      have h : (AST.Typ.primitive.fn AST.Typ.primitive : AST.Typ I) ≤ (AST.Typ.primitive.fn AST.Typ.primitive : AST.Typ I) := rfl
      simp [h]⟩
  · simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map]

example :
    (TypeHinted.hintedIdFnOnFalse.recCanInhabit .primitive).shouldYields () := by
  constructor
  · exact ⟨3, by
      simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map, TypeHinted.hintedIdFnOnFalse, TypeHinted.hintedIdFn, TypeHinted.hintedFalse]
      have h : (AST.Typ.primitive : AST.Typ I) ≤ (AST.Typ.primitive : AST.Typ I) := rfl
      simp [h]⟩
  · simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map]

example :
    ∀ typ, (Malformed.applyidFnOnItself.recCanInhabit typ).shouldFail := by
  intro typ
  constructor
  · refine ⟨3, ?_⟩
    simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map, Malformed.applyidFnOnItself, primitiveIdFn]
    have h : ¬((AST.Typ.primitive.fn AST.Typ.primitive : AST.Typ I) ≤ AST.Typ.primitive) := by
      intro hle; injection hle
    simp [h]
  · simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map]

example :
    ∀ typ, (Malformed.idFnOnFalse2.recCanInhabit typ).shouldFail := by
  intro typ
  constructor
  · refine ⟨4, ?_⟩
    simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map, Malformed.idFnOnFalse2, Malformed.applyidFnOnItself, primitiveIdFn, vFalse]
    have h : ¬((AST.Typ.primitive.fn AST.Typ.primitive : AST.Typ I) ≤ AST.Typ.primitive) := by
      intro hle; injection hle
    simp [h]
  · simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map]

example :
    ∀ typ, (Malformed.apply1.recCanInhabit typ).shouldFail := by
  intro typ
  constructor
  · refine ⟨4, ?_⟩
    simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map, Malformed.apply1, primitiveIdFn, vFalse, vTrue]
    have h : (AST.Typ.primitive : AST.Typ I) ≤ (AST.Typ.primitive : AST.Typ I) := rfl
    simp [h]
  · simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map]

example :
    ∀ typ, (Malformed.primitiveApply.recCanInhabit typ).shouldFail := by
  intro typ
  constructor
  · exact ⟨2, by cases typ <;> simp [AST.Trm.recCanInhabit, AST.Trm.infer, Outcome.map, Malformed.primitiveApply, vFalse, vTrue]⟩
  · rfl

end compile

end Trm

end Sanity
