import «Tests».STLC_Eval.TrmDemo

namespace Tests.STLC_Eval.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.STLC
open Tests.STLC_Eval.Sanity.Symbolic

namespace Fixture

@[reducible] unsafe def _unsafeFixpoint (T : Type) :
    I.Fixpoint T :=
  let saved : IO.Ref (Array T) := unsafeBaseIO (IO.mkRef #[])
  let getUID : T → I.Index := fun value =>
    unsafeBaseIO do
      let values ← saved.get
      saved.set (values.push value)
      pure (unsafeCast values.size)
  let inv : I.Index → T := fun ref =>
    let index : Nat := unsafeCast ref
    match (unsafeBaseIO saved.get)[index]? with
    | some t => t
    | none => unsafeCast ()
  {
    getUID := fun value => getUID value
    inv := fun ref => inv ref
    leftInv := by
      intro value
      exact unsafeCast True.intro
    rightInv := by
      intro id
      cases id
  }

@[reducible] unsafe def _runtimeEnv : @RuntimeEnv I :=
  {
    mkFixpoint := _unsafeFixpoint
    mkAux := λ _outer _M => {
      Receipt := λ _ => True
      getEv := λ _bundle => True.intro
      invEv := λ _ev => unsafeCast True.intro
    }
    mkAux0 := λ _ _ => unsafeCast True.intro
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
    let ref := env.trm2valCtx.getUID ⟨vFalse, Val.vFalse⟩
    (AST.ref ref).eval 1 = .yield (some Val.vFalse) := by
  simp [AST.eval]

example : (primitiveIdFnOnFalse : Trm).eval 1 = .outOfFuel := rfl

example : (primitiveIdFnOnFalse : Trm).eval.shouldYields Val.vFalse := by
  constructor
  · exact ⟨2, by simp [AST.eval, primitiveIdFnOnFalse, primitiveIdFn, vFalse, Val.idFn]⟩
  · rfl

example : (primitiveTrueFnOnFalse : Trm).eval.shouldYields Val.vTrue := by
  constructor
  · exact ⟨2, rfl⟩
  · rfl

example : (get1stOnTuple : Trm).eval.shouldYields Val.vFalse := by
  constructor
  · exact ⟨3, by simp [AST.eval, get1stOnTuple, get1st, vFalse, vTrue]⟩
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
