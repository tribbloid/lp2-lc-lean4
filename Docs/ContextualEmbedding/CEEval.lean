import «ContextualEmbedding».CE

namespace ContextualEmbedding.CE

open Ty

namespace STLC

/-- STLC value syntax for unit and function values in a configurable context. -/
inductive Val : Ctx -> Ty -> Type where
  | Star {ctx : Ctx} : Val ctx .Unit
  | Lambda {ctx : Ctx} {input output : Ty}
      (body : STLC (ctx :/: input) output) : Val ctx (input :-> output)
deriving Repr, DecidableEq

/-- STLC values with no free variables. -/
abbrev ClosedVal (ty : Ty) : Type := Val .Empty ty

end STLC

namespace STLCCtx

inductive Val : Ctx -> Ty -> Type where
  | CStar {ctx : Ctx} : Val ctx .Unit
  | CLam {ctx : Ctx} {input output : Ty}
      (body : ProxyTop (ctx :/: input) input ->
        STLCCtx (ctx :/: input) output) :
      Val ctx (input :-> output)

/-- Contextually embedded value syntax with no free variables. -/
abbrev ClosedVal (ty : Ty) : Type := Val .Empty ty

/-- Closed runtime values interpret object-language functions as HOAS functions. -/
def ClosedValRT : Ty -> Type
  | .Unit => PUnit
  | .Fun input output =>
      ClosedValRT input -> Nat -> Option (ClosedValRT output)

/-- A typed store of closed values for the variables in a contextual term. -/
class RuntimeEnv (ctx : Ctx) where
  lookup {ty : Ty} (index : Index ctx ty) : ClosedValRT ty

namespace RuntimeEnv

@[reducible] def empty : RuntimeEnv .Empty where
  lookup index := nomatch index

/-- Adds a closed value as the newest runtime binding. -/
@[reducible] def snoc (prev : RuntimeEnv ctx) (value : ClosedValRT ty) :
    RuntimeEnv (ctx :/: ty) where
  lookup
    | .Top => value
    | .Pop index => prev.lookup index

/-- Loads the value denoted by a contextual variable proxy. -/
def load (env : RuntimeEnv ctx) {source : Ctx}
    [inst : ReifyIndex source ctx]
    (proxy : ProxyTop source ty) : ClosedValRT ty :=
  env.lookup (ReifyIndex.reify (self := inst) proxy)

end RuntimeEnv

/-- Evaluates contextual syntax while spending one fuel at each semantic descent. -/
def eval (env : RuntimeEnv ctx) (term : STLCCtx ctx ty) :
    Nat -> Option (ClosedValRT ty)
  | 0 => .none
  | fuel + 1 =>
    match term with
    | .CStar => .some .unit
    | @STLCCtx.CVar _ _ _ inst proxy =>
        .some (env.load (inst := inst) proxy)
    | .CLam body =>
        .some (λ input => eval (env.snoc input) (body .PTop))
    | .CApp fn arg =>
        let fnValue := eval env fn fuel
        let argValue := eval env arg fuel
        match fnValue, argValue with
        | .some fnValue, .some argValue => fnValue argValue fuel
        | _, _ => .none

namespace Examples

def vFalse : STLCCtx .Empty .Unit := .CStar

def vTrue : STLCCtx .Empty .Unit := .CStar

def primitiveIdFn : STLCCtx .Empty (.Unit :-> .Unit) :=
  .CLam (λ input => .CVar input)

def primitiveIdFnOnFalse : STLCCtx .Empty .Unit :=
  .CApp primitiveIdFn vFalse

def get1st : STLCCtx .Empty (.Unit :-> .Unit :-> .Unit) :=
  .CLam (λ first => .CLam (λ _second => .CVar first))

def get2nd : STLCCtx .Empty (.Unit :-> .Unit :-> .Unit) :=
  .CLam (λ _first => .CLam (λ second => .CVar second))

def get1stOnTuple : STLCCtx .Empty .Unit :=
  .CApp (.CApp get1st vFalse) vTrue

def get2ndOnTuple : STLCCtx .Empty .Unit :=
  .CApp (.CApp get2nd vFalse) vTrue

example : eval .empty primitiveIdFnOnFalse 0 = .none := by
  rfl

example : eval .empty primitiveIdFnOnFalse 2 = .some .unit := by
  rfl

example : eval .empty get1stOnTuple 3 = .some .unit := by
  rfl

example : eval .empty get2ndOnTuple 3 = .some .unit := by
  rfl

end Examples


end STLCCtx

end ContextualEmbedding.CE
