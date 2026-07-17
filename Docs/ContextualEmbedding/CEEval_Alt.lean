import «ContextualEmbedding».CE

namespace ContextualEmbedding.CE

open Ty

namespace STLCCtx

inductive Val : Ctx -> Ty -> Type where
  | CStar {ctx : Ctx} : Val ctx .Unit
  | CLam {ctx : Ctx} {input output : Ty}
      (body : ProxyTop (ctx :/: input) input ->
        STLCCtx (ctx :/: input) output) :
      Val ctx (input :-> output)

/-- Contextually embedded value syntax with no free variables. -/
abbrev ClosedVal (ty : Ty) : Type := Val .Empty ty

/-- A runtime stack retaining each previous lexical environment. -/
inductive RuntimeEnv : Ctx -> Type where
  | empty : RuntimeEnv .Empty
  | saved {ctx valueCtx : Ctx} {ty : Ty}
      (previous : RuntimeEnv ctx)
      (valueEnv : RuntimeEnv valueCtx)
      (value : Val valueCtx ty) : RuntimeEnv (ctx :/: ty)

/-- A contextual value suspended with the environment in which it was produced. -/
structure Closure (ty : Ty) : Type where
  {ctx : Ctx}
  env : RuntimeEnv ctx
  value : Val ctx ty

namespace RuntimeEnv

/-- Loads the suspended value selected by a contextual index. -/
def lookup : (env : RuntimeEnv ctx) -> Index ctx ty -> Closure ty
  | .saved _ valueEnv value, .Top => ⟨valueEnv, value⟩
  | .saved previous _ _, .Pop index => previous.lookup index

/-- Loads the suspended value denoted by a contextual variable proxy. -/
def load (env : RuntimeEnv ctx) {source : Ctx}
    [inst : ReifyIndex source ctx]
    (proxy : ProxyTop source ty) : Closure ty :=
  env.lookup (ReifyIndex.reify (self := inst) proxy)

end RuntimeEnv

/-- Evaluates contextual syntax while spending one fuel at each semantic descent. -/
def eval (env : RuntimeEnv ctx) (term : STLCCtx ctx ty) :
    Nat -> Option (Closure ty)
  | 0 => .none
  | fuel + 1 =>
    match term with
    | .CStar => .some (.mk env .CStar)
    | @STLCCtx.CVar _ _ _ inst proxy =>
        .some (env.load (inst := inst) proxy)
    | .CLam body =>
        .some (.mk env (.CLam body))
    | .CApp fn arg =>
        let fnC := eval env fn fuel
        let argC := eval env arg fuel
        match fnC, argC with
        | .some (.mk fnEnv (.CLam body)), .some (.mk argEnv argValue) =>
            eval (.saved fnEnv argEnv argValue) (body .PTop) fuel
        | _, _ => .none

namespace Spike



end Spike

-- namespace Spike

-- /-- A runtime stack retaining each previous lexical environment. -/
-- inductive RuntimeEnv : Ctx -> Type where
--   | empty : RuntimeEnv Ctx.Empty
--   | saved {ctx valueCtx : Ctx} {ty : Ty}
--       (previous : RuntimeEnv ctx)
--       (value : Val valueCtx ty) :
--       RuntimeEnv (ctx :/: ty)

-- /-- A contextual value suspended with the environment in which it was produced. -/
-- structure Closure (ty : Ty) : Type where
--   {ctx : Ctx}
--   value : Val ctx ty

-- namespace RuntimeEnv

-- /-- Loads the suspended value selected by a contextual index. -/
-- def load : (env : RuntimeEnv ctx) -> Index ctx ty -> Closure ty
--   | saved _ value, .Top => ⟨value⟩
--   | saved previous _, .Pop index => previous.load index

-- end RuntimeEnv

-- /-- Evaluates contextual syntax while spending one fuel at each semantic descent. -/
-- def eval (env : RuntimeEnv ctx) (term : STLCCtx ctx ty) :
--     Nat -> Option (Closure ty)
--   | 0 => none
--   | fuel + 1 =>
--     match term with
--     | .CStar => some (.mk .CStar)
--     | @STLCCtx.CVar _ _ _ inst proxy =>
--         some (env.load (ReifyIndex.reify (self := inst) proxy))
--     | .CLam body =>
--         some (.mk (.CLam body))
--     | .CApp fn arg =>
--         let fnC := eval env fn fuel
--         let argC := eval env arg fuel
--         match fnC, argC with
--         | some (.mk (.CLam body)), some (.mk argValue) =>
--             eval (.saved env argValue) (body .PTop) fuel -- justified using 2 different context
--         | _, _ => none

-- end Spike

-- namespace SuspendedVal

-- /-- Compiles a suspended HOAS value again without changing its representation. -/
-- def compile (self : SuspendedVal ty) : Nat -> Option (SuspendedVal ty)
--   | 0 => none
--   | _ + 1 => some self

-- @[simp] theorem compile_succ (self : SuspendedVal ty) (fuel : Nat) :
--     self.compile (fuel + 1) = some self := by
--   rfl

-- theorem compile_idempotent (self : SuspendedVal ty) (fuel : Nat) :
--     (self.compile (fuel + 1)).bind
--       (fun value => value.compile (fuel + 1)) =
--     self.compile (fuel + 1) := by
--   simp

-- end SuspendedVal

namespace AltExamples

def vFalse : STLCCtx .Empty .Unit := .CStar

def vTrue : STLCCtx .Empty .Unit := .CStar

def primitiveIdFn : STLCCtx .Empty (.Unit :-> .Unit) :=
  .CLam (fun input => .CVar input)

def primitiveIdFnOnFalse : STLCCtx .Empty .Unit :=
  .CApp primitiveIdFn vFalse

def get1st : STLCCtx .Empty (.Unit :-> .Unit :-> .Unit) :=
  .CLam (fun first => .CLam (fun _second => .CVar first))

def get1stOnTuple : STLCCtx .Empty .Unit :=
  .CApp (.CApp get1st vFalse) vTrue

section variable (env : RuntimeEnv .Empty)

example : eval env vFalse 0 = .none := by
  rfl

example : eval env vFalse 1 = .some (.mk env .CStar) := by
  rfl

example : Option (Closure (.Unit :-> .Unit)) :=
  eval env primitiveIdFn 1

example : eval env primitiveIdFn 1 =
    .some (.mk env (.CLam (fun input => .CVar input))) := by
  rfl

example : eval env primitiveIdFnOnFalse 0 = .none := by
  rfl

example : eval env primitiveIdFnOnFalse 2 = .some (.mk env .CStar) := by
  rfl

example : eval env get1stOnTuple 3 = .some (.mk env .CStar) := by
  rfl

-- example (value : SuspendedVal ty) :
--     (value.compile 1).bind (fun compiled => compiled.compile 1) =
--       value.compile 1 := by
--   exact value.compile_idempotent 0

end

end AltExamples

end STLCCtx

end ContextualEmbedding.CE
