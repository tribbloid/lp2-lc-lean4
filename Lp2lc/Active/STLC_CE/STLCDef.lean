import Std
import «Lp2lc».Active.Util

namespace Lp2lc.Active

namespace STLC_CE

open Lp2lc.Active.Util

namespace AST

/-- Primitive payloads used by the closed CE version of STLC. -/
structure Data : Type
deriving DecidableEq, Repr

/--
Source type syntax.

`primitive` classifies primitive values and `fn` classifies functions.
-/
inductive Typ : Type where
| primitive
| fn (tIn : Typ) (tOut : Typ)
deriving DecidableEq, Repr

/-- Current STLC subtyping coincides with structural type equality. -/
instance typLE : LE Typ := ⟨Eq⟩

/-- Decides the current structural subtyping relation. -/
instance typDecidableLE : DecidableLE Typ
  | .primitive, .primitive => isTrue rfl
  | .primitive, .fn _ _
  | .fn _ _, .primitive => isFalse (fun equality => nomatch equality)
  | .fn leftIn leftOut, .fn rightIn rightOut =>
    match typDecidableLE leftIn rightIn, typDecidableLE leftOut rightOut with
    | isTrue inputEqual, isTrue outputEqual => isTrue (inputEqual ▸ outputEqual ▸ rfl)
    | isFalse notEqual, _ => isFalse (fun equality => notEqual (Typ.fn.inj equality).1)
    | _, isFalse notEqual => isFalse (fun equality => notEqual (Typ.fn.inj equality).2)

/-- CE typing contexts used by variable proxies. -/
inductive Ctx : Type where
| empty
| snoc (ctx : Ctx) (typ : Typ)
deriving DecidableEq, Repr

infixl:90 " :/: " => Ctx.snoc

/-- De Bruijn indices into CE contexts. -/
inductive Index : Ctx -> Type where
| top {ctx : Ctx} {typ : Typ} : Index (ctx :/: typ)
| pop {ctx : Ctx} {typ : Typ} : Index ctx -> Index (ctx :/: typ)
deriving DecidableEq, Repr

/-- Extrinsic evidence that an index points at a value of a type. -/
inductive Lookup : (ctx : Ctx) -> Index ctx -> Typ -> Type where
| top {ctx : Ctx} {typ : Typ} : Lookup (ctx :/: typ) .top typ
| pop {ctx : Ctx} {typ typ' : Typ} {index : Index ctx} :
    Lookup ctx index typ -> Lookup (ctx :/: typ') (.pop index) typ
deriving Repr

/-- The most recently bound variable of a CE context. -/
inductive ProxyTop : Ctx -> Type where
| ptop {ctx : Ctx} {typ : Typ} : ProxyTop (ctx :/: typ)
deriving DecidableEq, Repr

/-- Reifies a contextual top proxy into an index of a larger use context. -/
class ReifyIndex (source : Ctx) (ctx : Ctx) where
  reify : ProxyTop source -> Index ctx

instance instReifyIndexRefl : ReifyIndex ctx ctx where
  reify
    | .ptop => .top

instance instReifyIndexSnoc [instRec : ReifyIndex source ctx] :
    ReifyIndex source (ctx :/: typ) where
  reify := fun proxy => .pop (ReifyIndex.reify (self := instRec) proxy)

mutual

/--
Source term syntax.

Terms are indexed by their CE context but not by their result type, so typing
remains extrinsic while bound references are represented by CE proxy evidence.
-/
inductive Trm : Ctx -> Type where
| val {ctx : Ctx} (value : Val ctx) : Trm ctx
| apply {ctx : Ctx} (fn : Trm ctx) (arg : Trm ctx) : Trm ctx
| ref {source ctx : Ctx} [inst : ReifyIndex source ctx] :
    ProxyTop source -> Trm ctx

/--
Value syntax.

Function values carry their CE body and input type in the same context as the
term that contains them.
-/
inductive Val : Ctx -> Type where
| primitive {ctx : Ctx} (repr : Data) : Val ctx
| fn {ctx : Ctx} (tIn : Typ)
    (body : ProxyTop (ctx :/: tIn) -> Trm (ctx :/: tIn)) : Val ctx

end

/--
Typed contextual syntax.

The reference case mirrors `STLCCtx.CVar`: it types a contextual proxy by
reifying it into the current context and proving a lookup for that index.
-/
inductive HasType : (ctx : Ctx) -> Trm ctx -> Typ -> Type where
| valPrimitive {ctx : Ctx} {repr : Data} :
    HasType ctx (.val (.primitive repr)) .primitive
| valFn {ctx : Ctx} {tIn tOut : Typ}
    {body : ProxyTop (ctx :/: tIn) -> Trm (ctx :/: tIn)} :
    ((proxy : ProxyTop (ctx :/: tIn)) -> HasType (ctx :/: tIn) (body proxy) tOut) ->
    HasType ctx (.val (.fn tIn body)) (.fn tIn tOut)
| ref {source ctx : Ctx} {typ : Typ} [inst : ReifyIndex source ctx]
    (proxy : ProxyTop source) :
    Lookup ctx (ReifyIndex.reify (self := inst) proxy) typ ->
    HasType ctx (.ref proxy) typ
| apply {ctx : Ctx} {tIn tOut : Typ} {fn arg : Trm ctx} :
    HasType ctx fn (.fn tIn tOut) -> HasType ctx arg tIn ->
    HasType ctx (.apply fn arg) tOut

/-- Contextual variables paired with their reification evidence. -/
inductive ProxyVar (ctx : Ctx) where
| pvar {source : Ctx} [inst : ReifyIndex source ctx] :
    ProxyTop source -> ProxyVar ctx
deriving Repr

namespace ProxyVar

def weaken {ctx : Ctx} {typ : Typ} : ProxyVar ctx -> ProxyVar (ctx :/: typ)
  | @pvar _ _source _ proxy => pvar proxy

end ProxyVar

def varTop {ctx : Ctx} {typ : Typ} : ProxyVar (ctx :/: typ) :=
  .pvar (.ptop (ctx := ctx) (typ := typ))

def fromIndex : Index ctx -> ProxyVar ctx
  | .top => varTop
  | .pop index => (fromIndex index).weaken

def toRef (index : Index ctx) : Trm ctx :=
  match fromIndex index with
  | @ProxyVar.pvar _ _ inst proxy => .ref (inst := inst) proxy

namespace Trm


/--
Runtime lexical environments.

`snoc env value` extends `env` with one newest binding, while older bindings
remain reachable through `Index.pop`.
-/
inductive RuntimeEnv : Ctx -> Type where
| empty : RuntimeEnv .empty
| snoc {ctx valueCtx : Ctx} {typ : Typ}
    (env : RuntimeEnv ctx) (valueEnv : RuntimeEnv valueCtx) (value : Val valueCtx) :
    RuntimeEnv (ctx :/: typ)

namespace RuntimeEnv

/-- Resolves a runtime index by walking the lexical environment. -/
def lookup {ctx : Ctx} (env : RuntimeEnv ctx) :
    Index ctx -> (valueCtx : Ctx) × RuntimeEnv valueCtx × Val valueCtx
  | .top =>
    match env with
    | .snoc _ valueEnv value => ⟨_, valueEnv, value⟩
  | .pop index =>
    match env with
    | .snoc env _ _ => env.lookup index

end RuntimeEnv

/--
Evaluates a term by spending one fuel at each semantic descent.

Runtime reference resolution follows `ReifyIndex` into a lexical environment.
-/
def eval {ctx : Ctx} (self : Trm ctx)
    (env : RuntimeEnv ctx) : RecOption ((valueCtx : Ctx) × RuntimeEnv valueCtx × Val valueCtx)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield (some ⟨ctx, env, value⟩)
    | .apply fn arg =>
      match eval fn env fuel, eval arg env fuel with
      | .yield (some ⟨_, savedEnv, .fn _tIn body⟩), .yield (some ⟨_, inputEnv, input⟩) =>
        eval (body .ptop) (savedEnv.snoc inputEnv input) fuel
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none
    | @Trm.ref _source _ inst proxy =>
      .yield (some (env.lookup (ReifyIndex.reify (self := inst) proxy)))

end Trm

end AST

end STLC_CE

end Lp2lc.Active
