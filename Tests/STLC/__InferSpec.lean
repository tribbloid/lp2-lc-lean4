import «Lp2lc».Active.STLC.__Infer
import «Tests».STLC.Fixture

namespace Tests.STLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.Util.Rec
open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

section infer
variable [env : @CompilerEnv Symbolic.I]

example :
    (vFalse.infer).shouldYields .primitive := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    (primitiveIdFn.infer).shouldYields (.fn .primitive .primitive) := by
  constructor
  · exact ⟨2, by simp [AST.Trm.infer, Outcome.map, primitiveIdFn]⟩
  · rfl

example :
    (primitiveIdFnOnFalse.infer).shouldYields .primitive := by
  constructor
  · refine ⟨3, ?_⟩
    have hPrimitive : (AST.Typ.primitive : Typ) ≤ .primitive := by
      rfl
    simp [AST.Trm.infer, Outcome.map, primitiveIdFnOnFalse, primitiveIdFn, vFalse, hPrimitive]
  · rfl

example :
    (get1st.infer).shouldYields (.fn .primitive (.fn .primitive .primitive)) := by
  constructor
  · exact ⟨3, by simp [AST.Trm.infer, Outcome.map, get1st]⟩
  · rfl

example :
    (get1stOnTuple.infer).shouldYields .primitive := by
  constructor
  · refine ⟨5, ?_⟩
    have hPrimitive : (AST.Typ.primitive : Typ) ≤ .primitive := by
      rfl
    simp [AST.Trm.infer, Outcome.map, get1stOnTuple, get1st, vFalse, vTrue, hPrimitive]
  · rfl

example :
    (primitiveTrueFnOnFalse.infer).shouldYields .primitive := by
  constructor
  · refine ⟨3, ?_⟩
    have hPrimitive : (AST.Typ.primitive : Typ) ≤ .primitive := by
      rfl
    simp [AST.Trm.infer, Outcome.map, primitiveTrueFnOnFalse, primitiveTrueFn, vFalse, hPrimitive]
  · rfl

example :
    (Malformed.applyIdFnOnItself.infer).shouldFail := by
  constructor
  · refine ⟨3, ?_⟩
    have hFnNotPrimitive : ¬ ((AST.Typ.fn .primitive .primitive : Typ) ≤ .primitive) := by
      intro h
      cases h
    simp [AST.Trm.infer, Outcome.map, Malformed.applyIdFnOnItself, primitiveIdFn, hFnNotPrimitive]
  · rfl

example :
    (Malformed.primitiveApply.infer).shouldFail := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

end infer

end Trm

end Sanity
