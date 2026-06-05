import «Tests».DTLC.TrmDemo

namespace Tests.DTLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.DTLC
open Lp2lc.Active.DTLC.Symbolic

namespace Fixture

@[reducible] def RuntimeCanEval : Permission Val := fun _value => True

@[reducible] unsafe def _evalEnv : Runtime.Env impl :=
  let savedVals : IO.Ref (Array Val) := unsafeBaseIO (IO.mkRef #[])
  let saveVal : Val → impl.I := fun value =>
    unsafeBaseIO do
      let values ← savedVals.get
      savedVals.set (values.push value)
      pure (unsafeCast values.size)
  let loadVal : impl.I → Val := fun ref =>
    let index : Nat := unsafeCast ref
    match (unsafeBaseIO savedVals.get)[index]? with
    | some value => value
    | none => unsafeCast ()
  {
    EvalPermission := RuntimeCanEval
    forVals := {
      save := fun value _permission => saveVal value
      load := fun ref => loadVal ref
      roundtrip := by
        intro value
        intro permission
        exact unsafeCast True.intro
    }
    canEvalAny := fun _value => True.intro
  }

@[reducible] unsafe def _typingEnv : Compiletime.Env impl :=
  let saved : IO.Ref (Array Typ) := unsafeBaseIO (IO.mkRef #[])
  let save : Typ → impl.I := fun typ =>
    unsafeBaseIO do
      let values ← saved.get
      saved.set (values.push typ)
      pure (unsafeCast values.size)
  let loadVal : impl.I → Typ := fun ref =>
    let index : Nat := unsafeCast ref
    match (unsafeBaseIO saved.get)[index]? with
    | some t => t
    | none => unsafeCast ()
  {
    forTyps := {
      save := fun typ _permission => save typ
      load := fun ref => loadVal ref
      roundtrip := by
        intro value
        intro permission
        exact unsafeCast True.intro
    }
  }

@[instance, implemented_by _evalEnv]
axiom env : Runtime.Env impl -- this instance of Runtime.Env is intend to contain the unsafe part and not making it contaminating examples

end Fixture

end Trm

end Tests.DTLC.Sanity
