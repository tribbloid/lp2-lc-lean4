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
  ev := λ _ => True
  uid2val := testEnv.trm2valExe
  uid2valCtx := testEnv.trm2valExeCtx

instance : BEq (AST.Val (ExeEnv.Parameters env)) :=
  ⟨λ a b => astBEq a b (λ _ _ => true) litEq⟩

attribute [local simp] AST.eval
attribute [local simp] Binder.apply
attribute [local simp] Trm.vFalse Trm.vTrue Trm.primitiveIdFn Trm.primitiveIdFnOnFalse
attribute [local simp] Trm.get1st Trm.get2nd Trm.get1stOnTuple Trm.get2ndOnTuple
attribute [local simp] Trm.primitiveTrueFn Trm.primitiveTrueFnOnFalse
attribute [local simp] Trm.Malformed.applyIdFnOnItself Trm.Malformed.idFnOnFalse2
attribute [local simp] Trm.Malformed.apply1 Trm.Malformed.primitiveApply Val.idFn
attribute [local simp] Trm.FreeCapture.receipt Trm.FreeCapture.directRef Trm.FreeCapture.capturedRef
attribute [local simp] Trm.FreeCapture.capturedRefOnFalse

#guard (AST.recarrier (Q := ExeEnv.Parameters env) Trm.vFalse
  (λ receipt => ⟨receipt, True.intro⟩) id).eval.shouldYieldsBool 1 (.lit "false")

#guard (AST.recarrier (Q := ExeEnv.Parameters env) Trm.primitiveIdFnOnFalse
  (λ receipt => ⟨receipt, True.intro⟩) id).eval.shouldYieldsBool 2 (.lit "false")

#guard (AST.recarrier (Q := ExeEnv.Parameters env) Trm.get1stOnTuple
  (λ receipt => ⟨receipt, True.intro⟩) id).eval.shouldYieldsBool 3 (.lit "false")

#guard (AST.recarrier (Q := ExeEnv.Parameters env) Trm.get2ndOnTuple
  (λ receipt => ⟨receipt, True.intro⟩) id).eval.shouldYieldsBool 3 (.lit "true")

#guard (AST.recarrier (Q := ExeEnv.Parameters env) Trm.Malformed.applyIdFnOnItself
  (λ receipt => ⟨receipt, True.intro⟩) id).eval.shouldYieldsBool 2
  (Val.idFn.recarrier (Q := ExeEnv.Parameters env) (λ receipt => ⟨receipt, True.intro⟩) id)

#guard (AST.recarrier (Q := ExeEnv.Parameters env) Trm.Malformed.idFnOnFalse2
  (λ receipt => ⟨receipt, True.intro⟩) id).eval.shouldYieldsBool 3 (.lit "false")

#guard (AST.recarrier (Q := ExeEnv.Parameters env) Trm.Malformed.apply1
  (λ receipt => ⟨receipt, True.intro⟩) id).eval.shouldFailBool 3

#guard (AST.recarrier (Q := ExeEnv.Parameters env) Trm.Malformed.primitiveApply
  (λ receipt => ⟨receipt, True.intro⟩) id).eval.shouldFailBool 2

example : True := by
  fail_if_success
    have _body : Binder refs.Parameters .trm :=
      λ receipt => .ref receipt
  trivial

#guard (AST.recarrier (Q := ExeEnv.Parameters env) Trm.primitiveTrueFnOnFalse
  (λ receipt => ⟨receipt, True.intro⟩) id).eval.shouldYieldsBool 2 (.lit "true")

#guard (AST.recarrier (Q := ExeEnv.Parameters env) Trm.FreeCapture.directRef
  (λ receipt => ⟨receipt, True.intro⟩) id).eval.shouldYieldsBool 1
  (Trm.FreeCapture.value.recarrier (Q := ExeEnv.Parameters env)
    (λ receipt => ⟨receipt, True.intro⟩) id)

#guard (AST.recarrier (Q := ExeEnv.Parameters env) Trm.FreeCapture.capturedRefOnFalse
  (λ receipt => ⟨receipt, True.intro⟩) id).eval.shouldYieldsBool 2
  (Trm.FreeCapture.value.recarrier (Q := ExeEnv.Parameters env)
    (λ receipt => ⟨receipt, True.intro⟩) id)

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
