import «ContextualEmbedding».CE

namespace ContextualEmbedding.CE

namespace Runtime

mutual

/--
Runtime values for contextual STLC terms.

A function value is a closure: it stores the lexical environment from the point
where the lambda was evaluated, together with the contextual body.
-/
inductive Val : Ty -> Type where
  | star : Val Ty.Unit
  | closure {ts : Ctx} {a b : Ty}
      (env : Env ts)
      (body : ProxyTop (ts :/: a) a -> STLCCtx (ts :/: a) b)
      : Val (a :-> b)

/--
Runtime lexical environments indexed by the same context as the term.

`snoc env value` is the new lexical frame: `value` is available at `Index.Top`,
and every older binding in `env` remains available under one `Index.Pop`.
-/
inductive Env : Ctx -> Type where
  | empty : Env Ctx.Empty
  | snoc {ts : Ctx} {t : Ty} (env : Env ts) (value : Val t) : Env (ts :/: t)

end

namespace Env

/--
Look up a runtime value by its de Bruijn index.

The `Top` case reads the newest frame, while `Pop` moves through that frame and
continues in the preserved outer environment.
-/
def lookup (env : Env ts) (index : Index ts t) : Val t :=
  match env, index with
  | .snoc _ value, .Top => value
  | .snoc env _, .Pop index => env.lookup index

end Env

namespace Val

def describe (value : Val t) : String :=
  match value with
  | .star => "star"
  | .closure _ _ => "<closure>"

end Val

end Runtime

namespace STLCCtx

open Runtime

/--
Evaluate contextual STLC syntax using immutable lexical environments.

Application creates a fresh frame with `savedEnv.snoc argValue`; no `ProxyTop`
is stored as a mutable runtime location.
-/
def eval (expr : STLCCtx ts t) (env : Env ts) (fuel : Nat) : Option (Val t) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match expr with
      | .CStar => some .star
      | @STLCCtx.CVar _ _ _ inst proxy =>
          some (env.lookup (ReifyIndex.reify (self := inst) proxy))
      | .CLam body => some (.closure env body)
      | .CApp fn arg => do
          let fnValue <- fn.eval env fuel
          let argValue <- arg.eval env fuel
          match fnValue with
          | @Val.closure savedTs argTy _ savedEnv body =>
            -- this is where things are different (between this Snoc Env and my UID Env):
            -- in UID Env, argValue must be saved to get the UID
            -- but in this Snoc Env, the proxy can be obtained by just counting the length of the Ctx
            -- which one is better?
            let proxy := ProxyTop.PTop (ts := savedTs) (t := argTy)
            (body proxy).eval (savedEnv.snoc argValue) fuel
termination_by fuel

end STLCCtx

namespace Runtime.Examples

open Runtime

def showResult (result : Option (Val t)) : String :=
  match result with
  | none => "none"
  | some value => value.describe

def idStar : Option (Val Ty.Unit) :=
  (STLCCtx.CApp idSTLC' STLCCtx.CStar).eval Env.empty 4

def constStar : Option (Val Ty.Unit) :=
  (STLCCtx.CApp (STLCCtx.CApp const' STLCCtx.CStar) STLCCtx.CStar).eval Env.empty 8

example (env : Env ts) (outer : Val a) (inner : Val b) :
    ((env.snoc outer).snoc inner).lookup (Index.Pop Index.Top) = outer := by
  rfl

#eval showResult idStar
#eval showResult constStar

end Runtime.Examples

end ContextualEmbedding.CE
