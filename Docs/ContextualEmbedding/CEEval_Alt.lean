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

/-- Runtime operations for closing functions and saving arguments for HOAS bodies. -/
class RuntimeEnv (ctx : Ctx) where
  load {ty : Ty} (index : Index ctx ty) : ClosedVal ty
  closeLam {input output : Ty}
      (body : ProxyTop (ctx :/: input) input ->
        STLCCtx (ctx :/: input) output) :
    ClosedVal (input :-> output)
  save {input output : Ty} (argument : ClosedVal input)
      (body : ProxyTop (Ctx.Empty :/: input) input ->
        STLCCtx (Ctx.Empty :/: input) output) : ClosedVal output

/-- Evaluates contextual syntax while spending one fuel at each semantic descent. -/
def eval (env : RuntimeEnv ctx) (term : STLCCtx ctx ty) :
    Nat -> Option (ClosedVal ty)
  | 0 => none
  | fuel + 1 =>
    match term with
    | .CStar => some .CStar
    | @STLCCtx.CVar _ _ _ inst proxy =>
        some (env.load (ReifyIndex.reify (self := inst) proxy))
    | .CLam body =>
        some (env.closeLam body) -- TODO: construct the body of Val.CLam from the body of STLCCtx.CLam
    | .CApp fn argument =>
        let fnValue := eval env fn fuel
        let argValue := eval env argument fuel
        match fnValue, argValue with
        | some (.CLam body), some argValue => some (env.save argValue body)
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

example (env : RuntimeEnv Ctx.Empty) : eval env vFalse 0 = none := by
  rfl

example (env : RuntimeEnv Ctx.Empty) : eval env vFalse 1 = some .CStar := by
  rfl

example (env : RuntimeEnv Ctx.Empty) : Option (ClosedVal (Unit :-> Unit)) :=
  eval env primitiveIdFn 1

example (env : RuntimeEnv Ctx.Empty) : eval env primitiveIdFnOnFalse 1 = none := by
  rfl

example (env : RuntimeEnv Ctx.Empty) : Option (ClosedVal Unit) :=
  eval env primitiveIdFnOnFalse 2

example (env : RuntimeEnv Ctx.Empty) : Option (ClosedVal Unit) :=
  eval env get1stOnTuple 3

end AltExamples

end STLCCtx

end ContextualEmbedding.CE
