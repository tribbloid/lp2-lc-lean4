import «Tests».STLC.Fixture

namespace Tests.STLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

section eval
class TestEnv where
  mkUId4Val : CanGetUIdFor (λ T => AST.Val { C := T, D := String })

variable [testEnv : TestEnv]

@[reducible] instance env : ExeEnv := { D := String, mkUId4Val := testEnv.mkUId4Val }

def upcast {l : Label} (self : AST Symbolic.I l) : AST env.ExeParameters l :=
  self.map (F := Symbolic.I) (G := env.ExeParameters) (λ (s : Symbol) => nomatch s) id

attribute [local simp] AST.eval AST.map upcast
attribute [local simp] Trm.vFalse Trm.vTrue Trm.primitiveIdFn Trm.primitiveIdFnOnFalse
attribute [local simp] Trm.get1st Trm.get2nd Trm.get1stOnTuple Trm.get2ndOnTuple
attribute [local simp] Trm.primitiveTrueFn Trm.primitiveTrueFnOnFalse
attribute [local simp] Trm.Malformed.applyIdFnOnItself Trm.Malformed.idFnOnFalse2
attribute [local simp] Trm.Malformed.apply1 Trm.Malformed.primitiveApply Val.idFn

example : (upcast Trm.vFalse).eval.shouldYields (.lit "false") := by
  constructor
  · exact ⟨1, by simp⟩
  · rfl

example : (upcast Trm.primitiveIdFnOnFalse).eval.shouldYields (.lit "false") := by
  constructor
  · exact ⟨2, by simp⟩
  · rfl

example : (upcast Trm.get1stOnTuple).eval.shouldYields (.lit "false") := by
  constructor
  · exact ⟨3, by simp⟩
  · rfl

example : (upcast Trm.get2ndOnTuple).eval.shouldYields (.lit "true") := by
  constructor
  · exact ⟨3, by simp⟩
  · rfl

example : (upcast Trm.Malformed.applyIdFnOnItself).eval.shouldYields (upcast Val.idFn) := by
  constructor
  · exact ⟨2, by simp⟩
  · rfl

example : (upcast Trm.Malformed.idFnOnFalse2).eval.shouldYields (.lit "false") := by
  constructor
  · exact ⟨3, by simp⟩
  · rfl

example : (upcast Trm.Malformed.apply1).eval.shouldFail := by
  constructor
  · exact ⟨4, by simp⟩
  · rfl

example : (upcast Trm.Malformed.primitiveApply).eval.shouldFail := by
  constructor
  · exact ⟨2, by simp⟩
  · rfl

example : (upcast Trm.primitiveTrueFnOnFalse).eval.shouldYields (.lit "true") := by
  constructor
  · exact ⟨2, by simp⟩
  · rfl

end eval

end Trm

end Sanity
