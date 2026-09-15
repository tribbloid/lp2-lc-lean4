import «Tests».STLC.TrmDemo
import «Lp2lc».Active.STLC.__Infer

namespace Tests.STLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

/-- Compares two string literals without relying on the reducibility of the fixture's `D`. -/
def litEq (repr expected : String) : Bool := repr == expected

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

/-- Whether `t` evaluates to the string literal `expected` within `fuel`. -/
def evalYieldsLit (t : Trm) (fuel : Nat) (expected : String) : Bool :=
  match t.eval fuel with
  | .yield (some (.lit repr)) => litEq repr expected
  | _ => false

/-- Whether `t` evaluation fails within `fuel`. -/
def evalFails (t : Trm) (fuel : Nat) : Bool :=
  match t.eval fuel with
  | .yield none => true
  | _ => false

/-- Whether `t` evaluates to the identity function value within `fuel`. -/
def evalYieldsIdFn (t : Trm) (fuel : Nat) : Bool :=
  match t.eval fuel with
  | .yield (some (.lam (.mk (.ref (.inr ()))) .primitive)) => true
  | _ => false

#guard evalYieldsLit Trm.vFalse 1 "false"

#guard evalYieldsLit Trm.primitiveIdFnOnFalse 2 "false"

#guard evalYieldsLit Trm.get1stOnTuple 3 "false"

#guard evalYieldsLit Trm.get2ndOnTuple 3 "true"

#guard evalYieldsIdFn Trm.Malformed.applyIdFnOnItself 2

#guard evalYieldsLit Trm.Malformed.idFnOnFalse2 3 "false"

#guard evalFails Trm.Malformed.apply1 4

#guard evalFails Trm.Malformed.primitiveApply 2

example : True := by
  fail_if_success
    have _body : Binder refs.Parameters .trm :=
      λ receipt => .ref receipt
  trivial

#guard evalYieldsLit Trm.primitiveTrueFnOnFalse 2 "true"

#guard evalYieldsLit Trm.FreeCapture.directRef 1 "false"

#guard evalYieldsLit Trm.FreeCapture.capturedRefOnFalse 2 "false"

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
