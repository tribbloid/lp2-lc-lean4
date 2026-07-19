import «ContextualEmbedding».«3_ExtrinsicTyping».CE

namespace ContextualEmbedding.ExtrinsicTyping.CE

open Ty

namespace STLCCtx

/-- Contextually embedded value syntax with no free variables. -/
abbrev ClosedVal : Type := ValCtx .Empty

/-- A runtime stack retaining each previous lexical environment. -/
inductive RuntimeEnv : Ctx -> Type where
  | empty : RuntimeEnv .Empty
  | saved {ctx valueCtx : Ctx}
      (previous : RuntimeEnv ctx)
      (valueEnv : RuntimeEnv valueCtx)
      (value : ValCtx valueCtx) : RuntimeEnv (ctx :/)

/-- A contextual value suspended with the environment in which it was produced. -/
structure Closure : Type where
  {ctx : Ctx}
  env : RuntimeEnv ctx
  value : ValCtx ctx

namespace RuntimeEnv

/-- Loads the suspended value selected by a contextual index. -/
def lookup : (env : RuntimeEnv ctx) -> Index ctx -> Closure
  | .saved _ valueEnv value, .Top => ⟨valueEnv, value⟩
  | .saved previous _ _, .Pop index => previous.lookup index

/-- Loads the suspended value denoted by a contextual variable proxy. -/
def load (env : RuntimeEnv ctx) {source : Ctx}
    [inst : ReifyIndex source ctx]
    (proxy : ProxyTop source) : Closure :=
  env.lookup (ReifyIndex.reify (self := inst) proxy)

end RuntimeEnv

/-- Evaluates contextual syntax while spending one fuel at each semantic descent. -/
def eval (env : RuntimeEnv ctx) (term : STLCCtx ctx) :
    Nat -> Option Closure
  | 0 => .none
  | fuel + 1 =>
    match term with
    | .CVal .CStar => .some (.mk env .CStar)
    | @STLCCtx.CVar _ _ inst proxy =>
        .some (env.load (inst := inst) proxy)
    | .CVal (.CLam body) =>
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

def vFalse : STLCCtx .Empty := .CVal .CStar

def vTrue : STLCCtx .Empty := .CVal .CStar

def primitiveIdFn : STLCCtx .Empty :=
  .CVal (.CLam (λ input => .CVar input))

def primitiveIdFnOnFalse : STLCCtx .Empty :=
  .CApp primitiveIdFn vFalse

def get1st : STLCCtx .Empty :=
  .CVal (.CLam (λ first => .CVal (.CLam (λ _second => .CVar first))))

def get1stOn1st: STLCCtx .Empty := .CApp get1st vFalse

def get1stOnTuple : STLCCtx .Empty :=
  .CApp get1stOn1st vTrue

def captureFn : STLCCtx .Empty :=
  .CVal (.CLam (λ fn => .CVal (.CLam (λ _ => .CVar fn))))

def capturePrimitiveId :=
  STLCCtx.CApp captureFn primitiveIdFn

def captureGet1stOn1st : STLCCtx .Empty :=
  .CApp captureFn get1stOn1st


example : eval .empty vFalse 0 = .none := by
  rfl

example : eval .empty vFalse 1 = .some (.mk .empty .CStar) := by
  rfl

example : Option Closure :=
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

abbrev _ctx := .Empty :/

abbrev _env : RuntimeEnv _ctx := .saved .empty .empty .CStar

def result : Option Closure :=
  let _v : ValCtx _ctx :=
    .CLam (λ (_second : ProxyTop (_ctx :/)) =>
      .CVar (.PTop : ProxyTop _ctx))
  .some (.mk _env _v)

example : eval .empty get1stOn1st 3 =
    result := by
  rfl

end get1stOn1st

namespace captureFn

abbrev _v : ValCtx .Empty :=
  .CLam (λ fn => .CVal (.CLam (λ _ => .CVar fn)))

def result : Option Closure :=
  .some (.mk .empty _v)

example : eval .empty captureFn 3 =
    result := by
  rfl

end captureFn

namespace captureGet1stOn1st

def result : Option Closure :=
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

end ContextualEmbedding.ExtrinsicTyping.CE
