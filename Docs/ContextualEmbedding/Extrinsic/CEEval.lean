import «ContextualEmbedding».Extrinsic.CE

namespace ContextualEmbedding.Extrinsic.CE

inductive CtxHasType : (ts : Ctx) -> STLCCtx ts -> Ty -> Type where
  | CVar : (lookup : Lookup ts i t) -> CtxHasType ts (toCVar i) t
  | CStar : CtxHasType ts STLCCtx.CStar Ty.Unit
  | CLam : ((proxy : ProxyTop (ts :/: a)) -> CtxHasType (ts :/: a) (body proxy) b) ->
      CtxHasType ts (STLCCtx.CLam (ts := ts) a body) (a :-> b)
  | CApp : CtxHasType ts e1 (a :-> b) -> CtxHasType ts e2 a ->
      CtxHasType ts (STLCCtx.CApp e1 e2) b

namespace Runtime

mutual

/--
Runtime values for extrinsically typed contextual STLC terms.

A function value is a closure: it stores the lexical environment from the point
where the lambda was evaluated, together with the contextual body and its
extrinsic typing witness.
-/
inductive Val : Ty -> Type where
  | star : Val Ty.Unit
  | closure {ts : Ctx} {a b : Ty}
      (env : Env ts)
      (body : ProxyTop (ts :/: a) -> STLCCtx (ts :/: a))
      (bodyTyped : (proxy : ProxyTop (ts :/: a)) -> CtxHasType (ts :/: a) (body proxy) b)
      : Val (a :-> b)

/--
Runtime lexical environments indexed by the same context as the typing witness.

`snoc env value` is the new lexical frame: `value` is available through a
`Lookup.Top` proof, and every older binding in `env` remains available under
one `Lookup.Pop`.
-/
inductive Env : Ctx -> Type where
  | empty : Env Ctx.Empty
  | snoc {ts : Ctx} {t : Ty} (env : Env ts) (value : Val t) : Env (ts :/: t)

end

namespace Env

/--
Look up a runtime value by extrinsic lookup evidence.

The `Top` case reads the newest frame, while `Pop` moves through that frame and
continues in the preserved outer environment.
-/
def lookup (env : Env ts) (lookup : Lookup ts index t) : Val t :=
  match env, lookup with
  | .snoc _ value, .Top => value
  | .snoc env _, .Pop lookup => env.lookup lookup

end Env

namespace Val

def describe (value : Val t) : String :=
  match value with
  | .star => "star"
  | .closure _ _ _ => "<closure>"

end Val

end Runtime

namespace STLCCtx

open Runtime

/--
Evaluate contextual STLC syntax using immutable lexical environments.

The syntax is raw, so evaluation follows a `CtxHasType` witness. Application
creates a fresh frame with `savedEnv.snoc argValue`; no `ProxyTop` is stored as
a mutable runtime location.
-/
def eval (typed : CtxHasType ts expr t) (env : Env ts) (fuel : Nat) : Option (Val t) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match typed with
      | CtxHasType.CStar => some .star
      | CtxHasType.CVar lookup =>
          some (env.lookup lookup)
      | @CtxHasType.CLam _ _ body _ bodyTyped =>
          some (.closure env body bodyTyped)
      | CtxHasType.CApp fnTyped argTyped => do
          let fnValue <- eval fnTyped env fuel
          let argValue <- eval argTyped env fuel
          match fnValue with
          | @Val.closure savedTs argTy _ savedEnv body bodyTyped =>
            let proxy := ProxyTop.PTop (ts := savedTs) (t := argTy)
            eval (bodyTyped proxy) (savedEnv.snoc argValue) fuel
termination_by fuel

end STLCCtx

namespace Runtime.Examples

open Runtime

def idSTLCTyped {ts : Ctx} {a : Ty} : CtxHasType ts (@idSTLC ts a) (a :-> a) :=
  CtxHasType.CLam (fun x => by
    cases x
    exact CtxHasType.CVar Lookup.Top)

def idSTLCTyped' := @idSTLCTyped Ctx.Empty Ty.Unit

def constTyped {ts : Ctx} {a b : Ty} : CtxHasType ts (@const ts a b) (a :-> b :-> a) :=
  CtxHasType.CLam (fun x => by
    cases x
    exact CtxHasType.CLam (fun _y =>
      CtxHasType.CVar (Lookup.Pop Lookup.Top)))

def constTyped' := @constTyped Ctx.Empty Ty.Unit Ty.Unit

def showResult (result : Option (Val t)) : String :=
  match result with
  | none => "none"
  | some value => value.describe

def idStarTyped : CtxHasType Ctx.Empty (STLCCtx.CApp idSTLC' STLCCtx.CStar) Ty.Unit :=
  CtxHasType.CApp idSTLCTyped' CtxHasType.CStar

def idStar : Option (Val Ty.Unit) :=
  STLCCtx.eval idStarTyped Env.empty 4

def constStarTyped :
    CtxHasType Ctx.Empty (STLCCtx.CApp (STLCCtx.CApp const' STLCCtx.CStar) STLCCtx.CStar) Ty.Unit :=
  CtxHasType.CApp (CtxHasType.CApp constTyped' CtxHasType.CStar) CtxHasType.CStar

def constStar : Option (Val Ty.Unit) :=
  STLCCtx.eval constStarTyped Env.empty 8

example (env : Env ts) (outer : Val a) (inner : Val b) :
    ((env.snoc outer).snoc inner).lookup (Lookup.Pop Lookup.Top) = outer := by
  rfl

#eval showResult idStar
#eval showResult constStar

end Runtime.Examples

end ContextualEmbedding.Extrinsic.CE
