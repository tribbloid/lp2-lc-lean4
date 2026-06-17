import «Tests».STLC.TrmDemo

namespace Tests.STLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.STLC
open Tests.STLC.Sanity.Symbolic

namespace Fixture

@[reducible] def RuntimeCanEval : Permission Val := fun _value => True

/--
Build an `FBound` over an `IO.Ref (Array T)`. The permission is ignored
and `roundtrip` is discharged via `unsafeCast True.intro`; the bridge
is sound by construction.
-/
@[reducible] unsafe def _unsafeFBound (T : Type) :
    FBound I.Index T (fun _ => True) :=
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
    save := fun value _permission => save value
    load := fun ref => load ref
    roundtrip := by
      intro value
      intro permission
      exact unsafeCast True.intro
  }

@[reducible] unsafe def _runtimeEnv : @Runtime.Env I :=
  {
    EvalPermission := RuntimeCanEval
    valueRefs := _unsafeFBound Val
    canEvalAny := fun _value => True.intro
  }

@[reducible] unsafe def _compilerEnv : @Compiler.Env I :=
  {}

@[instance, implemented_by _runtimeEnv]
axiom runtimeEnv : @Runtime.Env I -- this instance of Runtime.Env is intend to contain the unsafe part and not making it contaminating examples

@[instance, implemented_by _compilerEnv]
axiom compilerEnv : @Compiler.Env I -- this instance of Runtime.Env is intend to contain the unsafe part and not making it contaminating examples

end Fixture

end Trm

end Tests.STLC.Sanity
