import «Tests».STLC_Eval.TrmDemo

namespace Tests.STLC_Eval.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.STLC
open Tests.STLC_Eval.Sanity.Symbolic

namespace Fixture

@[reducible] unsafe def _unsafeFBound (T : Type) :
    FBound I.Index T :=
  let saved : IO.Ref (Array T) := unsafeBaseIO (IO.mkRef #[])
  let save : T → I.Index := fun value =>
    unsafeBaseIO do
      let values ← saved.get
      saved.set (values.push value)
      pure (unsafeCast values.size)
  let load : I.Index → T := fun ref =>
    let index : Nat := unsafeCast ref
    match (unsafeBaseIO saved.get)[index]? with
    | some t => t
    | none => unsafeCast ()
  {
    save := fun value => save value
    load := fun ref => load ref
    roundtrip := by
      intro value
      exact unsafeCast True.intro
  }

@[reducible] unsafe def _runtimeEnv : @RuntimeEnv I :=
  {
    valueCtx := _unsafeFBound Val
  }

@[instance, implemented_by _runtimeEnv]
axiom runtimeEnv : @RuntimeEnv I

end Fixture

section eval

variable [env : @RuntimeEnv Symbolic.I]

example : (vFalse : Trm).eval 0 = .outOfFuel := rfl

example : (vFalse : Trm).eval.shouldYields Val.vFalse := by
  constructor
  · exact ⟨1, rfl⟩
  · rfl

example :
    let ref := env.valueCtx.save Val.vFalse
    (AST.Trm.ref ref).eval 1 = .yield (some Val.vFalse) := by
  simp [AST.Trm.eval]

example : (primitiveIdFnOnFalse : Trm).eval 1 = .outOfFuel := rfl

example : (primitiveIdFnOnFalse : Trm).eval.shouldYields Val.vFalse := by
  constructor
  · exact ⟨2, by simp [AST.Trm.eval, primitiveIdFnOnFalse, primitiveIdFn, vFalse, Val.idFn]⟩
  · rfl

example : (primitiveTrueFnOnFalse : Trm).eval.shouldYields Val.vTrue := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

example : (get1stOnTuple : Trm).eval.shouldYields Val.vFalse := by
  constructor
  · exact ⟨3, by simp [AST.Trm.eval, get1stOnTuple, get1st, vFalse, vTrue]⟩
  · rfl

example : (.apply primitiveIdFnOnFalse vTrue : Trm).eval 2 = .outOfFuel := rfl

example : (.apply primitiveIdFn primitiveIdFnOnFalse : Trm).eval 2 = .outOfFuel := rfl

example : (Malformed.primitiveApply : Trm).eval.shouldFail := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

example : (Malformed.bodyFailsOnFalse : Trm).eval.shouldFail := by
  constructor
  · exact ⟨3, rfl⟩
  · rfl

example : (Malformed.idFnOnPrimitiveApply : Trm).eval.shouldFail := by
  constructor
  · exact ⟨3, rfl⟩
  · rfl

example : (Malformed.primitiveApplyOnFalse : Trm).eval.shouldFail := by
  constructor
  · exact ⟨3, rfl⟩
  · rfl

end eval

end Trm

end Sanity
