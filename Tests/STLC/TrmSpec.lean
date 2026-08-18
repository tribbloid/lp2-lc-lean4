import «Tests».STLC.Fixture

namespace Tests.STLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.STLC
open Lp2lc.Active.Util.Free (FixpointCtor)
open Tests.STLC.Sanity.Symbolic

section eval

variable [fixCtor : FixpointCtor]

/-- test-only execution environment over String data, its fixpoint bridge is left abstract. -/
instance env : ExeEnv := {
  D := String
  mkFixpoint := fixCtor.mkFixpoint
}

/-- Transports symbolic demo syntax into the test environment parameters. -/
def upcast {l : Label} (self : AST Symbolic.I l) : AST env.ExeParameters l :=
  let mC : Symbol → env.trm2valCtx.UId := λ (s : Symbol) => nomatch s
  self.map (F := Symbolic.I) (G := env.ExeParameters) mC id

attribute [local simp] AST.eval AST.map upcast
attribute [local simp]
  Trm.vFalse Trm.vTrue
  Trm.primitiveIdFn Trm.primitiveIdFnOnFalse
  Trm.get1st Trm.get2nd Trm.get1stOnTuple Trm.get2ndOnTuple
  Trm.primitiveTrueFn Trm.primitiveTrueFnOnFalse
  Trm.Malformed.applyIdFnOnItself Trm.Malformed.idFnOnFalse2
  Trm.Malformed.apply1 Trm.Malformed.primitiveApply
  Val.idFn

example :
    (upcast Trm.vFalse).eval.shouldYields (.lit "false") := by
  constructor
  · exact ⟨1, by simp⟩
  · rfl

example :
    (upcast Trm.primitiveIdFnOnFalse).eval.shouldYields (.lit "false") := by
  constructor
  · exact ⟨2, by simp⟩
  · rfl

example :
    (upcast Trm.get1stOnTuple).eval.shouldYields (.lit "false") := by
  constructor
  · exact ⟨3, by simp⟩
  · rfl

example :
    (upcast Trm.get2ndOnTuple).eval.shouldYields (.lit "true") := by
  constructor
  · exact ⟨3, by simp⟩
  · rfl

example :
    (upcast Trm.Malformed.applyIdFnOnItself).eval.shouldYields (upcast Val.idFn) := by
  constructor
  · exact ⟨2, by simp⟩
  · rfl

example :
    (upcast Trm.Malformed.idFnOnFalse2).eval.shouldYields (.lit "false") := by
  constructor
  · exact ⟨3, by simp⟩
  · rfl

example :
    (upcast Trm.Malformed.apply1).eval.shouldFail := by
  constructor
  · exact ⟨4, by simp⟩
  · rfl

example :
    (upcast Trm.Malformed.primitiveApply).eval.shouldFail := by
  constructor
  · exact ⟨2, by simp⟩
  · rfl

example :
    (upcast Trm.primitiveTrueFnOnFalse).eval.shouldYields (.lit "true") := by
  constructor
  · exact ⟨2, by simp⟩
  · rfl

end eval

end Trm

end Sanity
