import «ContextualEmbedding».CE

namespace ContextualEmbedding.CE

open Ty

namespace STLCCtx

inductive Val : Ctx -> Ty -> Type where
  | CStar {ctx : Ctx} : Val ctx Unit
  | CLam {ctx : Ctx} {input output : Ty}
      (body : ProxyTop (ctx :/: input) input ->
        STLCCtx (ctx :/: input) output) :
      Val ctx (input :-> output)

/-- Contextually embedded value syntax with no free variables. -/
abbrev ClosedVal (ty : Ty) : Type := Val Ctx.Empty ty

/-- Runtime operations for loading and saving contextual values. -/
class RuntimeEnv (ctx : Ctx) where
  load {ty : Ty} (index : Index ctx ty) : Val ctx ty

namespace RuntimeEnv

@[reducible] def empty : RuntimeEnv Ctx.Empty where
  load index := nomatch index

/-- Adds a closed value as the newest runtime binding. -/
@[reducible] def save (env : RuntimeEnv ctx)
  (value : Val (ctx :/: ty) ty) :
    RuntimeEnv (ctx :/: ty) where
  load
  | .Top => value
  | .Pop index => env.load index

end RuntimeEnv

/-- Evaluates contextual syntax while spending one fuel at each semantic descent. -/
def eval (env : RuntimeEnv ctx) (term : STLCCtx ctx ty) :
    Nat -> Option (Val ctx ty)
  | 0 => none
  | fuel + 1 =>
    match term with
    | .CStar => some .CStar
    | @STLCCtx.CVar _ _ _ inst proxy =>
        some (env.load (ReifyIndex.reify (self := inst) proxy))
    | .CLam body =>
        some (.CLam body)
    | .CApp fn argument =>
        let fnValue := eval env fn fuel
        let argValue := eval env argument fuel
        match fnValue, argValue with
        | some (.CLam body), some argValue => some (env.save argValue)
        | _, _ => none

namespace AltExamples

def vFalse : STLCCtx Ctx.Empty Unit := .CStar

def vTrue : STLCCtx Ctx.Empty Unit := .CStar

def primitiveIdFn : STLCCtx Ctx.Empty (Unit :-> Unit) :=
  .CLam (fun input => .CVar input)

def primitiveIdFnOnFalse : STLCCtx Ctx.Empty Unit :=
  .CApp primitiveIdFn vFalse

def get1st : STLCCtx Ctx.Empty (Unit :-> Unit :-> Unit) :=
  .CLam (fun first => .CLam (fun _second => .CVar first))

def get1stOnTuple : STLCCtx Ctx.Empty Unit :=
  .CApp (.CApp get1st vFalse) vTrue

section variable (env : RuntimeEnv Ctx.Empty):

example : eval env vFalse 0 = none := by
  rfl

example : eval env vFalse 1 = some .CStar := by
  rfl

example : Option (ClosedVal (Unit :-> Unit)) :=
  eval env primitiveIdFn 1

example : eval env primitiveIdFn 1 =
    some (.CLam (fun input => .CVar input)) := by
  rfl

example : eval env primitiveIdFnOnFalse 0 = none := by
  rfl

example : eval env primitiveIdFnOnFalse 2 = .some .CStar := by
  rfl

example : eval env get1stOnTuple 3 = .some .CStar := by
  rfl

end

end AltExamples

end STLCCtx

end ContextualEmbedding.CE
