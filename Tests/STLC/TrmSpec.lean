import «Tests».STLC.TrmDemo
import «Lp2lc».Active.STLC.__Infer

open Lp2lc.Active.Util
open Lp2lc.Active.STLC

namespace Tests.STLC.Sanity

namespace Trm

open Tests.STLC.Sanity.Symbolic

section eval
variable [testEnv : TestEnv] [testEnvString : TestEnv.StringData testEnv]

/-- Runtime context is the fixture's own executable view; its evidence domain
decides which receipts may fetch values, so no fake value can be forged. -/
@[reducible] instance env : ExeEnv refs := testEnv.exe

instance : BEq (AST.Val env.Parameters) :=
  ⟨λ a b => astBEq a b (λ _ _ => true) dEqLitEq⟩

attribute [local simp] AST.eval
attribute [local simp] Binder.apply
attribute [local simp] Trm.vFalse Trm.vTrue Trm.primitiveIdFn Trm.primitiveIdFnOnFalse
attribute [local simp] Trm.get1st Trm.get2nd Trm.get1stOnTuple Trm.get2ndOnTuple
attribute [local simp] Trm.primitiveTrueFn Trm.primitiveTrueFnOnFalse
attribute [local simp] Trm.Malformed.applyIdFnOnItself Trm.Malformed.idFnOnFalse2
attribute [local simp] Trm.Malformed.apply1 Trm.Malformed.primitiveApply Val.idFn
attribute [local simp] Trm.FreeCapture.receipt Trm.FreeCapture.directRef Trm.FreeCapture.capturedRef
attribute [local simp] Trm.FreeCapture.capturedRefOnFalse

#guard Trm.vFalse.eval.shouldYieldsBool 1 (.lit dFalse)

#guard Trm.primitiveIdFnOnFalse.eval.shouldYieldsBool 2 (.lit dFalse)

#guard Trm.get1stOnTuple.eval.shouldYieldsBool 3 (.lit dFalse)

#guard Trm.get2ndOnTuple.eval.shouldYieldsBool 3 (.lit dTrue)

#guard Trm.Malformed.applyIdFnOnItself.eval.shouldYieldsBool 2 Val.idFn

#guard Trm.Malformed.idFnOnFalse2.eval.shouldYieldsBool 3 (.lit dFalse)

#guard Trm.Malformed.apply1.eval.shouldFailBool 3

#guard Trm.Malformed.primitiveApply.eval.shouldFailBool 2

example : True := by
  fail_if_success
    have _body : Binder refs.Parameters .trm :=
      λ receipt => .ref receipt
  trivial

#guard Trm.primitiveTrueFnOnFalse.eval.shouldYieldsBool 2 (.lit dTrue)

#guard Trm.FreeCapture.directRef.eval.shouldYieldsBool 1 Trm.FreeCapture.value

#guard Trm.FreeCapture.capturedRefOnFalse.eval.shouldYieldsBool 2 Trm.FreeCapture.value

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
