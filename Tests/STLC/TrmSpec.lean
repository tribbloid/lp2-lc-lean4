import «Tests».STLC.Fixture

namespace Tests.STLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

section eval
variable [env : @ExeEnv Symbolic.I]

example :
    ((Trm.vFalse : Trm).eval).shouldYields
      ((.lit "false") : Val) := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    ((Trm.primitiveIdFnOnFalse : Trm).eval).shouldYields
      ((.lit "false") : Val) := by
  constructor
  · exact ⟨2, by simp [AST.eval, primitiveIdFnOnFalse, primitiveIdFn, vFalse]⟩
  · rfl

example :
    ((Trm.get1stOnTuple : Trm).eval).shouldYields
      ((.lit "false") : Val) := by
  constructor
  · exact ⟨3, by simp [AST.eval, get1stOnTuple, get1st, vFalse, vTrue]⟩
  · rfl

example :
    ((Trm.get2ndOnTuple : Trm).eval).shouldYields
      ((.lit "true") : Val) := by
  constructor
  · exact ⟨3, by simp [AST.eval, get2ndOnTuple, get2nd, vFalse, vTrue]⟩
  · rfl

example :
    (Malformed.applyIdFnOnItself.eval).shouldYields
      (Val.idFn : Val) := by
  constructor
  · exact ⟨2, by simp [AST.eval, Malformed.applyIdFnOnItself, primitiveIdFn, Val.idFn]⟩
  · rfl

example :
    ((Trm.Malformed.idFnOnFalse2 : Trm).eval).shouldYields
      ((.lit "false") : Val) := by
  constructor
  · exact ⟨3, by simp [AST.eval, Malformed.idFnOnFalse2, Malformed.applyIdFnOnItself, primitiveIdFn, vFalse]⟩
  · rfl

example :
    ((Trm.Malformed.apply1 : Trm).eval).shouldFail := by
  constructor
  · exact ⟨4, by simp [AST.eval, Malformed.apply1, primitiveIdFn, vFalse, vTrue]⟩
  · rfl

example :
    ((Trm.Malformed.primitiveApply : Trm).eval).shouldFail := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

example :
    ((Trm.primitiveTrueFnOnFalse : Trm).eval).shouldYields
      ((.lit "true") : Val) := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

end eval

end Trm

end Sanity
