import «Lp2lc».Active.STLC.Serial.Eval
import «Tests».STLC.TrmDemo

open Lp2lc.Active.Util
open Lp2lc.Active.STLC

namespace Tests.STLC.Sanity

namespace Trm

open Tests.STLC.Sanity.Symbolic

section eval
variable [testEnv : TestEnv]

/-- Runtime context is the fixture's own executable view, whose equivalence
mints receipts only from executable values. -/
@[reducible] instance env : ExeEnv refs := testEnv.exe

instance : BEq (AST.Val refs.Parameters) :=
  ⟨λ a b => astBEq a b (λ _ => .null) (λ repr => litSig repr)⟩

attribute [local simp] AST.eval
attribute [local simp] Binder.apply
attribute [local simp] Trm.vFalse Trm.vTrue Trm.primitiveIdFn Trm.primitiveIdFnOnFalse
attribute [local simp] Trm.get1st Trm.get2nd Trm.get1stOnTuple Trm.get2ndOnTuple
attribute [local simp] Trm.primitiveTrueFn Trm.primitiveTrueFnOnFalse
attribute [local simp] Trm.Malformed.WrongTypeIdFnOnItself Trm.Malformed.WrongTypeIdFnOnFalse2
attribute [local simp] Trm.Malformed.applyLit2 Trm.Malformed.applyLit1 Val.idFn
attribute [local simp] Trm.FreeCapture.receipt Trm.FreeCapture.directRef Trm.FreeCapture.capturedRef
attribute [local simp] Trm.FreeCapture.capturedRefOnFalse

#guard Trm.vFalse.eval.shouldYields 1 (.lit bFalse)

#guard Trm.primitiveIdFnOnFalse.eval.shouldYields 2 (.lit bFalse)

#guard Trm.get1stOnTuple.eval.shouldYields 3 (.lit bFalse)

#guard Trm.get2ndOnTuple.eval.shouldYields 3 (.lit bTrue)

#guard Trm.Malformed.WrongTypeIdFnOnItself.eval.shouldYields 2 Val.idFn

#guard Trm.Malformed.WrongTypeIdFnOnFalse2.eval.shouldYields 3 (.lit bFalse)

#guard Trm.Malformed.applyLit2.eval.shouldFail 3

#guard Trm.Malformed.applyLit1.eval.shouldFail 2

example : True := by
  fail_if_success
    have _body : Binder refs.Parameters .trm :=
      λ receipt => .ref receipt
  trivial

#guard Trm.primitiveTrueFnOnFalse.eval.shouldYields 2 (.lit bTrue)

#guard Trm.FreeCapture.directRef.eval.shouldYields 1 Trm.FreeCapture.value

#guard Trm.FreeCapture.capturedRefOnFalse.eval.shouldYields 2 Trm.FreeCapture.value

end eval

section compilerCapability -- FIXME: useless now, remove

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
