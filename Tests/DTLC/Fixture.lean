import «Tests».DTLC.TrmDemo

namespace Tests.DTLC.Sanity

namespace Trm

open Lp2lc.Active.Util
open Lp2lc.Active.DTLC
open Lp2lc.Active.DTLC.Symbolic

namespace Fixture

/--
Build a stateful testing approximation of [Free.Fixpoint] over an
`IO.Ref (Array T)`. [UIdEquiv.leftInv] is discharged via
`unsafeCast True.intro`; the pure structure remains hypothetical.
-/
@[reducible] unsafe def _unsafeFixpoint (T : Type) :
    F.Fixpoint T :=
  let saved : IO.Ref (Array T) := unsafeBaseIO (IO.mkRef #[])
  let getUId : T → F.Carrier := fun value =>
    unsafeBaseIO do
      let values ← saved.get
      saved.set (values.push value)
      pure (unsafeCast values.size)
  let inv : F.Carrier → T := fun ref =>
    let index : Nat := unsafeCast ref
    match (unsafeBaseIO saved.get)[index]? with
    | some t => t
    | none => unsafeCast ()
  {
    getUId := fun value => getUId value
    inv := fun ref => inv ref
    leftInv := by
      intro value
      exact unsafeCast True.intro
    rightInv := by
      intro id
      cases id
  }

@[reducible] unsafe def _runtimeEnv : @RuntimeEnv F :=
  {
    valueCtx := _unsafeFixpoint Val
  }


@[instance, implemented_by _runtimeEnv]
axiom runtimeEnv : @RuntimeEnv F -- this instance of Runtime.Env is intend to contain the unsafe part and not making it contaminating examples


@[reducible] unsafe def _compilerEnv : @CompilerEnv F :=
  {
    typeCtx := _unsafeFixpoint (AST.Typ F)
  }

@[instance, implemented_by _compilerEnv]
axiom compilerEnv : @CompilerEnv F -- this instance of Runtime.Env is intend to contain the unsafe part and not making it contaminating examples

end Fixture

end Trm

end Tests.DTLC.Sanity
