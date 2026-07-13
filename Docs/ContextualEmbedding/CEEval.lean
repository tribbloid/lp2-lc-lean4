import «ContextualEmbedding».CE

namespace ContextualEmbedding.CE

open Ty

namespace STLC

/-- STLC value syntax for unit and function values in a configurable context. -/
inductive Val : Ctx -> Ty -> Type where
  | Star {ctx : Ctx} : Val ctx Unit
  | Lambda {ctx : Ctx} {input output : Ty}
      (body : STLC (ctx :/: input) output) : Val ctx (input :-> output)
deriving Repr, DecidableEq

/-- STLC values with no free variables. -/
abbrev ClosedVal (ty : Ty) : Type := Val Ctx.Empty ty

end STLC

namespace STLCCtx

inductive Val : Ctx -> Ty -> Type where
  | CStar {ctx : Ctx} : Val ctx Unit
  | CLam {ctx : Ctx} {input output : Ty}
      (body : ProxyTop (ctx :/: input) input ->
        STLCCtx (ctx :/: input) output) :
      Val ctx (input :-> output)

/-- Contextually embedded value syntax with no free variables. -/
abbrev ClosedVal (ty : Ty) : Type := Val Ctx.Empty ty

/-- Closed runtime values interpret object-language functions as HOAS functions. -/
def ClosedValRT : Ty -> Type
  | Ty.Unit => PUnit
  | Ty.Fun input output => ClosedValRT input -> ClosedValRT output

/-- A typed store of closed values for the variables in a contextual term. -/
class RuntimeEnv (ctx : Ctx) where
  load {ty : Ty} (index : Index ctx ty) : ClosedValRT ty

namespace RuntimeEnv

@[reducible] def empty : RuntimeEnv Ctx.Empty where
  load index := nomatch index

/-- Adds a closed value as the newest runtime binding. -/
@[reducible] def snoc (env : RuntimeEnv ctx) (value : ClosedValRT ty) :
    RuntimeEnv (ctx :/: ty) where
  load
    | .Top => value
    | .Pop index => env.load index

end RuntimeEnv

/-- Evaluates contextual syntax to a closed value without names or substitution. -/
def eval (env : RuntimeEnv ctx) :
    (term : STLCCtx ctx ty) -> ClosedValRT ty
  | .CStar => PUnit.unit
  | @STLCCtx.CVar _ _ _ inst proxy =>
      env.load (ReifyIndex.reify (self := inst) proxy)
  | .CLam body =>
      fun input => eval (env.snoc input) (body .PTop)
  | .CApp fn arg =>
      eval env fn (eval env arg)

namespace Examples

def vFalse : STLCCtx Ctx.Empty Unit := .CStar

def vTrue : STLCCtx Ctx.Empty Unit := .CStar

def primitiveIdFn : STLCCtx Ctx.Empty (Unit :-> Unit) :=
  .CLam (fun input => .CVar input)

def primitiveIdFnOnFalse : STLCCtx Ctx.Empty Unit :=
  .CApp primitiveIdFn vFalse

def get1st : STLCCtx Ctx.Empty (Unit :-> Unit :-> Unit) :=
  .CLam (fun first => .CLam (fun _second => .CVar first))

def get2nd : STLCCtx Ctx.Empty (Unit :-> Unit :-> Unit) :=
  .CLam (fun _first => .CLam (fun second => .CVar second))

def get1stOnTuple : STLCCtx Ctx.Empty Unit :=
  .CApp (.CApp get1st vFalse) vTrue

def get2ndOnTuple : STLCCtx Ctx.Empty Unit :=
  .CApp (.CApp get2nd vFalse) vTrue

example : eval .empty primitiveIdFnOnFalse = PUnit.unit := by
  rfl

example : eval .empty primitiveIdFn PUnit.unit = PUnit.unit := by
  rfl

example : eval .empty get1stOnTuple = PUnit.unit := by
  rfl

example : eval .empty get2ndOnTuple = PUnit.unit := by
  rfl

end Examples


end STLCCtx

end ContextualEmbedding.CE
