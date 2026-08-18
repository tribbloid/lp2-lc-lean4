import «Tests».STLC.Fixture

namespace Tests.STLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.STLC
open Lp2lc.Next.Util
open Lp2lc.Next.Util.Free (Fixpoint)
open Tests.STLC.Sanity.Symbolic

universe u

section eval

/--
unsafe test-only fixpoint bridge: receipts are fake-cast to [Symbol] so the
symbolic demo terms can be evaluated without a lawful bridge.

Any roundtrip through the fake bridge is recovered by [rightInv]/[leftInv].
-/
unsafe def unsafeFixpoint (VK : UIdU → Type u) : Fixpoint VK :=
  { UId := Symbol,
    get := λ receipt => unsafeCast receipt,
    inv := λ value => unsafeCast value,
    rightInv := λ _value => unsafeCast True.intro,
    leftInv := λ _receipt => unsafeCast True.intro }

/-- unsafe test-only execution environment over the symbolic carrier and String data. -/
unsafe instance testEnv : ExeEnv := {
  D := String
  mkFixpoint := unsafeFixpoint
}

/-- Transports symbolic demo syntax into the test environment parameters. -/
unsafe def upcast {l : Label} (self : AST Symbolic.I l) : AST testEnv.ExeParameters l :=
  self.map (λ (s : Symbol) => nomatch s) id

unsafe example :
    (upcast Trm.vFalse).eval.shouldYields
      ((.lit "false") : AST.Val testEnv.ExeParameters) := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

unsafe example :
    (upcast Trm.primitiveIdFnOnFalse).eval.shouldYields
      ((.lit "false") : AST.Val testEnv.ExeParameters) := by
  constructor
  · exact ⟨2, by
      simp only [AST.eval, AST.map, upcast,
        Trm.primitiveIdFnOnFalse, Trm.primitiveIdFn, Trm.vFalse]
      rw (config := { transparency := .default }) [testEnv.trm2valCtx.rightInv]
      rfl⟩
  · rfl

unsafe example :
    (upcast Trm.get1stOnTuple).eval.shouldYields
      ((.lit "false") : AST.Val testEnv.ExeParameters) := by
  constructor
  · exact ⟨3, by
      simp only [AST.eval, AST.map, upcast,
        Trm.get1stOnTuple, Trm.get1st, Trm.vFalse, Trm.vTrue]
      rw (config := { transparency := .default }) [testEnv.trm2valCtx.rightInv]
      rfl⟩
  · rfl

unsafe example :
    (upcast Trm.get2ndOnTuple).eval.shouldYields
      ((.lit "true") : AST.Val testEnv.ExeParameters) := by
  constructor
  · exact ⟨3, by
      simp only [AST.eval, AST.map, upcast,
        Trm.get2ndOnTuple, Trm.get2nd, Trm.vFalse, Trm.vTrue]
      rw (config := { transparency := .default }) [testEnv.trm2valCtx.rightInv]
      rfl⟩
  · rfl

unsafe example :
    (upcast Trm.Malformed.applyIdFnOnItself).eval.shouldYields
      (upcast Val.idFn : AST.Val testEnv.ExeParameters) := by
  constructor
  · exact ⟨2, by
      simp only [AST.eval, AST.map, upcast,
        Trm.Malformed.applyIdFnOnItself, Trm.primitiveIdFn, Val.idFn]
      rw (config := { transparency := .default }) [testEnv.trm2valCtx.rightInv]⟩
  · rfl

unsafe example :
    (upcast Trm.Malformed.idFnOnFalse2).eval.shouldYields
      ((.lit "false") : AST.Val testEnv.ExeParameters) := by
  constructor
  · exact ⟨3, by
      simp only [AST.eval, AST.map, upcast,
        Trm.Malformed.idFnOnFalse2, Trm.Malformed.applyIdFnOnItself,
        Trm.primitiveIdFn, Trm.vFalse]
      rw (config := { transparency := .default }) [testEnv.trm2valCtx.rightInv]
      simp only [AST.eval, AST.map, upcast,
        Trm.Malformed.idFnOnFalse2, Trm.Malformed.applyIdFnOnItself,
        Trm.primitiveIdFn, Trm.vFalse]
      rw (config := { transparency := .default }) [testEnv.trm2valCtx.rightInv]
      rfl⟩
  · rfl

unsafe example :
    (upcast Trm.Malformed.apply1).eval.shouldFail := by
  constructor
  · exact ⟨4, by
      simp only [AST.eval, AST.map, upcast,
        Trm.Malformed.apply1, Trm.primitiveIdFn, Trm.vFalse, Trm.vTrue]
      rw (config := { transparency := .default }) [testEnv.trm2valCtx.rightInv]
      simp only [AST.eval, AST.map, upcast,
        Trm.Malformed.apply1, Trm.primitiveIdFn, Trm.vFalse, Trm.vTrue]⟩
  · rfl

unsafe example :
    (upcast Trm.Malformed.primitiveApply).eval.shouldFail := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

unsafe example :
    (upcast Trm.primitiveTrueFnOnFalse).eval.shouldYields
      ((.lit "true") : AST.Val testEnv.ExeParameters) := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

end eval

end Trm

end Sanity
