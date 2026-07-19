import «ContextualEmbedding».«3_ExtrinsicTyping».CE

namespace ContextualEmbedding.ExtrinsicTyping.CE

open Ty

namespace STLCCtx

/-- Contextually embedded value syntax with no free variables. -/
abbrev ClosedVal : Type := ValCtx 0

/-- A runtime stack retaining each previous lexical environment. -/
inductive RuntimeEnv : Ctx -> Type where
  | empty : RuntimeEnv 0
  | saved {ctx valueCtx : Ctx}
      (previous : RuntimeEnv ctx)
      (valueEnv : RuntimeEnv valueCtx)
      (value : ValCtx valueCtx) : RuntimeEnv (ctx + 1)

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
def load [inst : ReifyIndex ts ts'] (env : RuntimeEnv ts')
    (proxy : ProxyTop ts) : Closure :=
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

namespace AltExamples

def vFalse : STLCCtx 0 := .CVal .CStar

def vTrue : STLCCtx 0 := .CVal .CStar

def primitiveIdFn : STLCCtx 0 :=
  .CVal (.CLam (λ input => .CVar input))

def primitiveIdFnOnFalse : STLCCtx 0 :=
  .CApp primitiveIdFn vFalse

def get1st : STLCCtx 0 :=
  .CVal (.CLam (λ first => .CVal (.CLam (λ _second => .CVar first))))

def get1stOn1st: STLCCtx 0 := .CApp get1st vFalse

def get1stOnTuple : STLCCtx 0 :=
  .CApp get1stOn1st vTrue

def captureFn : STLCCtx 0 :=
  .CVal (.CLam (λ fn => .CVal (.CLam (λ _ => .CVar fn))))

def capturePrimitiveId :=
  STLCCtx.CApp captureFn primitiveIdFn

def captureGet1stOn1st : STLCCtx 0 :=
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

abbrev _ctx := 0 + 1

abbrev _env : RuntimeEnv _ctx := .saved .empty .empty .CStar -- the first argument is set, but wasn't consumed by STLCCtx.CVar, as a result, the RuntimeEnv cannot be empty.

def result : Option Closure :=
  let _v : ValCtx _ctx :=
    .CLam (λ (_second : ProxyTop (_ctx + 1)) =>
      .CVar (.PTop : ProxyTop _ctx))
  .some (.mk _env _v)

example : eval .empty get1stOn1st 3 =
    result := by
  rfl

end get1stOn1st

namespace captureFn

abbrev _v : ValCtx 0 :=
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
