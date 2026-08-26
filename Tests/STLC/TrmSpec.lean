import «Tests».STLC.TrmDemo
import «Lp2lc».Active.STLC.__Infer

namespace Tests.STLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

section eval
variable [testEnv : TestEnv]

@[reducible] instance env : ExeEnv refs := { uid2valCtx := testEnv.trm2valExeCtx }

attribute [local simp] AST.eval
attribute [local simp] Trm.vFalse Trm.vTrue Trm.primitiveIdFn Trm.primitiveIdFnOnFalse
attribute [local simp] Trm.get1st Trm.get2nd Trm.get1stOnTuple Trm.get2ndOnTuple
attribute [local simp] Trm.primitiveTrueFn Trm.primitiveTrueFnOnFalse
attribute [local simp] Trm.Malformed.applyIdFnOnItself Trm.Malformed.idFnOnFalse2
attribute [local simp] Trm.Malformed.apply1 Trm.Malformed.primitiveApply Val.idFn
attribute [local simp] Trm.FreeCapture.receipt Trm.FreeCapture.directRef Trm.FreeCapture.capturedRef
attribute [local simp] Trm.FreeCapture.capturedRefOnFalse

example : Trm.vFalse.eval.shouldYields (.lit "false") := by
  constructor
  · exact ⟨1, by simp⟩
  · rfl

example : Trm.primitiveIdFnOnFalse.eval.shouldYields (.lit "false") := by
  constructor
  · exact ⟨2, by simp⟩
  · rfl

example : Trm.get1stOnTuple.eval.shouldYields (.lit "false") := by
  constructor
  · exact ⟨3, by simp⟩
  · rfl

example : Trm.get2ndOnTuple.eval.shouldYields (.lit "true") := by
  constructor
  · exact ⟨3, by simp⟩
  · rfl

example : Trm.Malformed.applyIdFnOnItself.eval.shouldYields Val.idFn := by
  constructor
  · exact ⟨2, by simp <;> rfl⟩
  · rfl

example : Trm.Malformed.idFnOnFalse2.eval.shouldYields (.lit "false") := by
  constructor
  · exact ⟨3, by simp⟩
  · rfl

example : Trm.Malformed.apply1.eval.shouldFail := by
  constructor
  · exact ⟨4, by simp⟩
  · rfl

example : Trm.Malformed.primitiveApply.eval.shouldFail := by
  constructor
  · exact ⟨2, by simp⟩
  · rfl

example : Trm.primitiveTrueFnOnFalse.eval.shouldYields (.lit "true") := by
  constructor
  · exact ⟨2, by simp⟩
  · rfl

example : Trm.FreeCapture.directRef.eval.shouldYields Trm.FreeCapture.value := by
  constructor
  · exact ⟨1, by simp⟩
  · rfl

example : Trm.FreeCapture.capturedRefOnFalse.eval.shouldYields Trm.FreeCapture.value := by
  constructor
  · exact ⟨2, by simp⟩
  · rfl

end eval

section compilerCapability

variable [refs : ExeRefs] [build : BuildEnv refs]

example : True := by
  fail_if_success
    have _receipt := refs.uid2val.inv
  trivial

example : True := by
  fail_if_success
    have _exe : ExeEnv refs := inferInstance
  trivial

end compilerCapability

section structuralLambda

variable [testEnv : TestEnv]

example : True := by
  fail_if_success
    have _binderIdentityCounterexample : Trm :=
      .val (.lam (λ _lift arg => .ref (.inr arg)) .primitive)
  trivial

end structuralLambda

end Trm

end Sanity
