import «Tests».STLC.TrmDemo
import «Lp2lc».Active.STLC.__Infer

namespace Tests.STLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

section eval
variable [testEnv : TestEnv]

@[reducible] instance env : ExeEnv refs where
  uid2val := testEnv.trm2valExe.val
  uid2valCtx := testEnv.trm2valExeCtx

attribute [local simp] AST.eval
attribute [local simp] Binder.apply
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

example : True := by
  fail_if_success
    have _body : Binder refs.Parameters .trm :=
      λ receipt => .ref receipt
  trivial

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

example [build : BuildEnv refs] (upcast : build.uid2typ.upcastV.toFun = Sum.inr) :
    (AST.ref (build.uid2typCtx.inv (.primitive : AST.Typ refs.Parameters)).val : Trm).eval.shouldFail := by
  constructor
  · refine ⟨1, ?_⟩
    have hLookup := (build.uid2typ.equivariance (build.uid2typCtx.inv .primitive)).symm
    simp [AST.eval, hLookup, upcast]
  · rfl

end eval

section compilerCapability

variable [refs : HasUId2Any] [build : BuildEnv refs]

example : True := by
  fail_if_success
    have _receipt := refs.uid2any.inv
  trivial

example : True := by
  fail_if_success
    have _exe : ExeEnv refs := inferInstance
  trivial

example [_exe : ExeEnv refs] : True := by
  fail_if_success
    have _receipt := _exe.uid2typCtx.inv
  trivial

example : True := by
  fail_if_success
    have _receipt := build.uid2valCtx.inv
  trivial

end compilerCapability

end Trm

end Sanity
