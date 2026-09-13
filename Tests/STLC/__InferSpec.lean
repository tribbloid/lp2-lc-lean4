import «Lp2lc».Active.STLC.__Infer
import «Tests».STLC.TrmDemo

namespace Tests.STLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.Util.Rec
open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

section infer
variable [testEnv : TestEnv] [build : BuildEnv refs]
abbrev Typ := AST.Typ refs.Parameters

attribute [local simp] Binder.apply

variable (upcast : build.uid2typ.upcastV.toFun = Sum.inr)

include upcast
@[local simp]
theorem trm2typLookup
    (receipt : {uid // build.uid2typ.ev uid}) :
    refs.uid2any.get receipt.val = .inr (build.uid2typ.get receipt) :=
  (build.uid2typ.equivariance receipt).symm.trans (congrFun upcast _)

example :
    (vFalse.infer).shouldYields .primitive := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    (vTrue.infer).shouldYields .primitive := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    (primitiveIdFn.infer).shouldYields (.fn .primitive .primitive) := by
  constructor
  · exact ⟨2, by simp_all [AST.infer, Outcome.map, primitiveIdFn]⟩
  · rfl

example :
    (primitiveIdFnOnFalse.infer).shouldYields .primitive := by
  constructor
  · refine ⟨3, ?_⟩
    have hPrimitive : (AST.primitive : Typ) ≤ .primitive := by
      rfl
    simp_all [AST.infer, Outcome.map,
      primitiveIdFnOnFalse, primitiveIdFn, vFalse]
  · rfl

example :
    (get1st.infer).shouldYields (.fn .primitive (.fn .primitive .primitive)) := by
  constructor
  · exact ⟨3, by simp_all [AST.infer, Outcome.map, get1st]⟩
  · rfl

example :
    (get2nd.infer).shouldYields (.fn .primitive (.fn .primitive .primitive)) := by
  constructor
  · exact ⟨3, by simp_all [AST.infer, Outcome.map, get2nd]⟩
  · rfl

example :
    (get1stOnTuple.infer).shouldYields .primitive := by
  constructor
  · refine ⟨5, ?_⟩
    have hPrimitive : (AST.primitive : Typ) ≤ .primitive := by
      rfl
    simp_all [AST.infer, Outcome.map,
      get1stOnTuple, get1st, vFalse, vTrue]
  · rfl

example :
    (get2ndOnTuple.infer).shouldYields .primitive := by
  constructor
  · refine ⟨5, ?_⟩
    have hPrimitive : (AST.primitive : Typ) ≤ .primitive := by
      rfl
    simp_all [AST.infer, Outcome.map,
      get2ndOnTuple, get2nd, vFalse, vTrue]
  · rfl

example :
    (primitiveTrueFn.infer).shouldYields (.fn .primitive .primitive) := by
  constructor
  · exact ⟨2, by simp_all [AST.infer, Outcome.map, primitiveTrueFn]⟩
  · rfl

example :
    (primitiveTrueFnOnFalse.infer).shouldYields .primitive := by
  constructor
  · refine ⟨3, ?_⟩
    have hPrimitive : (AST.primitive : Typ) ≤ .primitive := by
      rfl
    simp_all [AST.infer, Outcome.map,
      primitiveTrueFnOnFalse, primitiveTrueFn, vFalse]
  · rfl

example :
    (TypeHinted.hintedFalse.infer).shouldYields .primitive := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    (TypeHinted.hintedIdFn.infer).shouldYields (.fn .primitive .primitive) := by
  constructor
  · exact ⟨2, by simp_all [AST.infer, Outcome.map,
      TypeHinted.hintedIdFn]⟩
  · rfl

example :
    (TypeHinted.hintedIdFnOnFalse.infer).shouldYields .primitive := by
  constructor
  · refine ⟨3, ?_⟩
    have hPrimitive : (AST.primitive : Typ) ≤ .primitive := by
      rfl
    simp_all [AST.infer, Outcome.map,
      TypeHinted.hintedIdFnOnFalse, TypeHinted.hintedIdFn,
      TypeHinted.hintedFalse]
  · rfl

example :
    (FreeCapture.directRef.infer).shouldYields .primitive := by
  constructor
  · exact ⟨2, by simp_all [AST.infer, AST.Val.asTrm, FreeCapture.directRef,
      FreeCapture.receipt, FreeCapture.value]⟩
  · rfl

example :
    (AST.ref (build.uid2typCtx.inv (.primitive : Typ)).val : Trm).infer.shouldYields
      .primitive := by
  constructor
  · exact ⟨1, by simp_all [AST.infer]⟩
  · rfl

example :
    (Malformed.applyIdFnOnItself.infer).shouldFail := by
  constructor
  · refine ⟨3, ?_⟩
    have hFnNotPrimitive :
        ¬ ((AST.fn .primitive .primitive : Typ) ≤ .primitive) := by
      intro h
      cases h
    simp_all [AST.infer, Outcome.map,
      Malformed.applyIdFnOnItself, primitiveIdFn]
  · rfl

example :
    (Malformed.idFnOnFalse2.infer).shouldFail := by
  constructor
  · refine ⟨4, ?_⟩
    have hFnNotPrimitive :
        ¬ ((AST.fn .primitive .primitive : Typ) ≤ .primitive) := by
      intro h
      cases h
    simp_all [AST.infer, Outcome.map,
      Malformed.idFnOnFalse2, Malformed.applyIdFnOnItself,
      primitiveIdFn, vFalse]
  · rfl

example :
    (Malformed.apply1.infer).shouldFail := by
  constructor
  · refine ⟨4, ?_⟩
    have hPrimitive : (AST.primitive : Typ) ≤ .primitive := by
      rfl
    simp_all [AST.infer, Outcome.map,
      Malformed.apply1, primitiveIdFn, vFalse, vTrue]
  · rfl

example :
    (Malformed.primitiveApply.infer).shouldFail := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

end infer

end Trm

end Sanity
