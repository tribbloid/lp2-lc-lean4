import «Tests».DTLC.TrmDemo

namespace Tests.DTLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.DTLC
open Lp2lc.Active.DTLC.Symbolic

namespace Fixture

@[reducible] def RuntimeCanEval : Permission Val := fun _value => True

/--
Build an `FBound` over an `IO.Ref (Array T)`. The permission is ignored
and `roundtrip` is discharged via `unsafeCast True.intro`; the bridge
is sound by construction.
-/
@[reducible] unsafe def _unsafeFBound (T : Type) :
    FBound F.Index T :=
  let saved : IO.Ref (Array T) := unsafeBaseIO (IO.mkRef #[])
  let save : T → F.Index := fun value =>
    unsafeBaseIO do
      let values ← saved.get
      saved.set (values.push value)
      pure (unsafeCast values.size)
  let load : F.Index → T := fun ref =>
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

@[reducible] unsafe def _runtimeEnv : @RuntimeEnv F :=
  {
    EvalPermission := RuntimeCanEval
    forVals := _unsafeFBound { value : Val // RuntimeCanEval value }
    canEvalAny := fun _value => True.intro
  }


@[instance, implemented_by _runtimeEnv]
axiom runtimeEnv : @RuntimeEnv F -- this instance of Runtime.Env is intend to contain the unsafe part and not making it contaminating examples


@[reducible] unsafe def _compilerEnv : @CompilerEnv F :=
  { forSemantic := _unsafeFBound { _semantic : Val -> AST.Condition F // True } }

@[instance, implemented_by _compilerEnv]
axiom compilerEnv : @CompilerEnv F -- this instance of Runtime.Env is intend to contain the unsafe part and not making it contaminating examples

end Fixture

end Trm

end Tests.DTLC.Sanity
