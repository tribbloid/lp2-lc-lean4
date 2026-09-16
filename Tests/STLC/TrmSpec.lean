import «Tests».STLC.TrmDemo
import «Lp2lc».Active.STLC.__Infer

open Lp2lc.Active.Util
open Lp2lc.Active.STLC

namespace Tests.STLC.Sanity

namespace Trm

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

#guard Trm.vFalse.eval.shouldYieldsBool 1 (.lit "false")

#guard Trm.primitiveIdFnOnFalse.eval.shouldYieldsBool 2 (.lit "false")

#guard Trm.get1stOnTuple.eval.shouldYieldsBool 3 (.lit "false")

#guard Trm.get2ndOnTuple.eval.shouldYieldsBool 3 (.lit "true")

#guard Trm.Malformed.applyIdFnOnItself.eval.shouldYieldsBool 2 Val.idFn

#guard Trm.Malformed.idFnOnFalse2.eval.shouldYieldsBool 3 (.lit "false")

#guard Trm.Malformed.apply1.eval.shouldFailBool 3

#guard Trm.Malformed.primitiveApply.eval.shouldFailBool 2

example : True := by
  fail_if_success
    have _body : Binder refs.Parameters .trm :=
      λ receipt => .ref receipt
  trivial

#guard Trm.primitiveTrueFnOnFalse.eval.shouldYieldsBool 2 (.lit "true")

#guard Trm.FreeCapture.directRef.eval.shouldYieldsBool 1 Trm.FreeCapture.value

#guard Trm.FreeCapture.capturedRefOnFalse.eval.shouldYieldsBool 2 Trm.FreeCapture.value

#guard (AST.ref ((inferInstance : BuildEnv refs).uid2typCtx.inv (.primitive : AST.Typ refs.Parameters)).val : Trm).eval.shouldFailBool 1

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
