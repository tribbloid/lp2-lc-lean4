import «Tests».STLC.Fixture

namespace Tests.STLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

section typeHint

example :
    TypeHinted.hintedFalse.typeHint.get =
      some (.primitive : Typ) := rfl

example :
    TypeHinted.hintedIdFn.typeHint.get =
      some (.fn .primitive .primitive : Typ) := rfl

example :
    TypeHinted.hintedIdFnOnFalse.typeHint.get =
      (none : Option Typ) := rfl

end typeHint

section eval
variable [env : @Runtime.Env Symbolic.I]

example :
    ((Trm.vFalse : Trm).eval).shouldYields
      ((.primitive "false") : Val) := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    ((Trm.primitiveIdFnOnFalse : Trm).eval).shouldYields
      ((.primitive "false") : Val) := by
  constructor
  · exact ⟨2, by simp [AST.Trm.eval, primitiveIdFnOnFalse, primitiveIdFn, vFalse]⟩
  · rfl

example :
    ((Trm.get1stOnTuple : Trm).eval).shouldYields
      ((.primitive "false") : Val) := by
  constructor
  · exact ⟨3, by simp [AST.Trm.eval, get1stOnTuple, get1st, vFalse, vTrue]⟩
  · rfl

example :
    ((Trm.get2ndOnTuple : Trm).eval).shouldYields
      ((.primitive "true") : Val) := by
  constructor
  · exact ⟨3, by simp [AST.Trm.eval, get2ndOnTuple, get2nd, vFalse, vTrue]⟩
  · rfl

example :
    ((Trm.Malformed.applyidFnOnItself : Trm).eval).shouldYields
      (Val.idFn : Val) := by
  constructor
  · exact ⟨2, by simp [AST.Trm.eval, Malformed.applyidFnOnItself, primitiveIdFn, Val.idFn]⟩
  · rfl

example :
    ((Trm.Malformed.idFnOnFalse2 : Trm).eval).shouldYields
      ((.primitive "false") : Val) := by
  constructor
  · exact ⟨3, by simp [AST.Trm.eval, Malformed.idFnOnFalse2, Malformed.applyidFnOnItself, primitiveIdFn, vFalse]⟩
  · rfl

example :
    ((Trm.Malformed.apply1 : Trm).eval).shouldFail := by
  constructor
  · exact ⟨4, by simp [AST.Trm.eval, Malformed.apply1, primitiveIdFn, vFalse, vTrue]⟩
  · rfl

example :
    ((Trm.Malformed.primitiveApply : Trm).eval).shouldFail := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

example :
    ((Trm.primitiveTrueFnOnFalse : Trm).eval).shouldYields
      ((.primitive "true") : Val) := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

end eval

section compile
variable [env : Compiler.Env Symbolic.I]

example :
    (vFalse.compile fun _ => true).isDecidable := by
  sorry

example :
    (vTrue.compile fun _ => true).isDecidable := by
  sorry

example :
    (primitiveIdFn.compile fun _ => true).isDecidable := by
  sorry

example :
    (primitiveIdFnOnFalse.compile fun _ => true).isDecidable := by
  sorry

example :
    (get1st.compile fun _ => true).isDecidable := by
  sorry

example :
    (get2nd.compile fun _ => true).isDecidable := by
  sorry

example :
    (get1stOnTuple.compile fun _ => true).isDecidable := by
  sorry

example :
    (get2ndOnTuple.compile fun _ => true).isDecidable := by
  sorry

example :
    (primitiveTrueFn.compile fun _ => true).isDecidable := by
  sorry

example :
    (primitiveTrueFnOnFalse.compile fun _ => true).isDecidable := by
  sorry

example :
    (TypeHinted.hintedFalse.compile fun _ => true).isDecidable := by
  sorry

example :
    (TypeHinted.hintedIdFn.compile fun _ => true).isDecidable := by
  sorry

example :
    (TypeHinted.hintedIdFnOnFalse.compile fun _ => true).isDecidable := by
  sorry

example :
    (Malformed.applyidFnOnItself.compile fun _ => true).shouldFail := by
  sorry

example :
    (Malformed.idFnOnFalse2.compile fun _ => true).shouldFail := by
  sorry

example :
    (Malformed.apply1.compile fun _ => true).shouldFail := by
  sorry

example :
    (Malformed.primitiveApply.compile fun _ => true).shouldFail := by
  sorry

example :
    (Malformed.primitiveFalseAsFn.compile fun _ => true).shouldFail := by
  sorry

example :
    (Malformed.idFnAsPrimitive.compile fun _ => true).shouldFail := by
  sorry

end compile

end Trm

end Sanity
