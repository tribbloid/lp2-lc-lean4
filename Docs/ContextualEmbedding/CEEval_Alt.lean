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
  .CLam (λ input => .CVar input)

def primitiveIdFnOnFalse : STLCCtx .Empty .Unit :=
  .CApp primitiveIdFn vFalse

def get1st : STLCCtx .Empty (.Unit :-> .Unit :-> .Unit) :=
  .CLam (λ first => .CLam (λ _second => .CVar first))

def get1stOn1st: STLCCtx .Empty (.Unit :-> .Unit) := .CApp get1st vFalse

def get1stOnTuple : STLCCtx .Empty .Unit :=
  .CApp get1stOn1st vTrue

def captureFn : STLCCtx .Empty ((.Unit :-> .Unit) :-> .Unit :-> (.Unit :-> .Unit)) :=
  .CLam (λ fn => .CLam (λ _ => .CVar fn))

def capturePrimitiveId :=
  STLCCtx.CApp captureFn primitiveIdFn

def captureGet1stOn1st : STLCCtx .Empty (.Unit :-> (.Unit :-> .Unit)) :=
  .CApp captureFn get1stOn1st


example : eval .empty vFalse 0 = .none := by
  rfl

example : eval .empty vFalse 1 = .some (.mk .empty .CStar) := by
  rfl

example : Option (Closure (.Unit :-> .Unit)) :=
  eval .empty primitiveIdFn 1

example : eval .empty primitiveIdFn 1 =
    .some (.mk .empty (.CLam (λ input => .CVar input))) := by
  rfl

example : eval .empty primitiveIdFnOnFalse 0 = .none := by
  rfl

example : eval .empty primitiveIdFnOnFalse 2 = .some (.mk .empty .CStar) := by
  rfl

example : eval .empty get1stOnTuple 3 = .some (.mk .empty .CStar) := by
  rfl

namespace get1stOn1st

abbrev _ctx := .Empty :/: .Unit

abbrev _env : RuntimeEnv _ctx := .saved .empty .empty .CStar

def result : Option (Closure (.Unit :-> .Unit)) :=
  let _v : Val _ctx (.Unit :-> .Unit) :=
    .CLam (λ (_second : ProxyTop (_ctx :/: .Unit) .Unit) =>
      .CVar (.PTop : ProxyTop _ctx .Unit))
  .some (.mk _env _v)

example : eval .empty get1stOn1st 3 =
    result := by
  rfl

end get1stOn1st

namespace captureFn

abbrev _v : Val .Empty
    ((.Unit :-> .Unit) :-> .Unit :-> (.Unit :-> .Unit)) :=
  .CLam (λ fn => .CLam (λ _ => .CVar fn))

def result : Option (Closure
    ((.Unit :-> .Unit) :-> .Unit :-> (.Unit :-> .Unit))) :=
  .some (.mk .empty _v)

example : eval .empty captureFn 3 =
    result := by
  rfl

end captureFn

namespace captureGet1stOn1st

def result : Option (Closure (.Unit :-> (.Unit :-> .Unit))) :=
  match captureFn.result, get1stOn1st.result with
  | .some (.mk fnEnv (.CLam body)), .some (.mk argEnv argValue) =>
      eval (.saved fnEnv argEnv argValue) (body .PTop) 3
  | _, _ => .none

example : eval .empty captureGet1stOn1st 4 = result := by
  rfl

end captureGet1stOn1st


-- example (value : SuspendedVal ty) :
--     (value.compile 1).bind (fun compiled => compiled.compile 1) =
--       value.compile 1 := by
--   exact value.compile_idempotent 0

end AltExamples

end STLCCtx

end ContextualEmbedding.CE
