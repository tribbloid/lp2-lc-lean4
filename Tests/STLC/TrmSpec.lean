import «Tests».STLC.Fixture
import «Lp2lc».Active.STLC.__Infer

namespace Tests.STLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

section eval
class TestEnv where
  trm2val : UIdView (λ T => AST.Val { C := T, D := String })
  trm2valCtx : UIdEquiv.Extendable.{3, 3}
    (VK := λ T => AST.Val { C := T, D := String }) (base := trm2val)

variable [testEnv : TestEnv]

@[reducible] instance core : EnvCore := { D := String, uid2val := testEnv.trm2val }
@[reducible] instance env : ExeEnv core := { uid2valCtx := testEnv.trm2valCtx }

def upcast {l : Label} (self : AST Symbolic.I l) : AST core.ExeParameters l :=
  self.map (F := Symbolic.I) (G := core.ExeParameters) (λ (s : Symbol) => nomatch s) id

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

section compilerCapability

variable [compilerCore : EnvCore] [build : BuildEnv compilerCore]

example : True := by
  fail_if_success
    have _receipt := compilerCore.uid2val.inv
  trivial

example : True := by
  fail_if_success
    have _exe : ExeEnv compilerCore := inferInstance
  trivial

end compilerCapability

end Trm

end Sanity
