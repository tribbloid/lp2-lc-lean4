import Std
import «Lp2lc».Active.Util

namespace Lp2lc.Active

namespace STLC_CE

open Lp2lc.Active.Util

namespace AST

/-- Primitive payloads used by the closed CE version of STLC. -/
inductive Data : Type where
| unit
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

/-- The most recently bound variable of a CE context. -/
inductive ProxyTop : Ctx -> Typ -> Type where
| ptop {ctx : Ctx} {typ : Typ} : ProxyTop (ctx :/: typ) typ
deriving Repr

mutual

/--
Source term syntax.

Terms are indexed by their CE context but not by their result type, so typing
remains extrinsic while bound references are represented by CE proxy evidence.
-/
inductive Trm : Ctx -> Type where
| val {ctx : Ctx} (value : Val) : Trm ctx
| apply {ctx : Ctx} (fn : Trm ctx) (arg : Trm ctx) : Trm ctx
| ref {ctx : Ctx} {typ : Typ} :
    ProxyTop ctx typ -> Trm ctx

/--
Value syntax.

Function values carry only their CE body and input type.
-/
inductive Val : Type where
| primitive (repr : Data)
| fn {ctx : Ctx} (tIn : Typ)
    (body : ProxyTop (ctx :/: tIn) tIn -> Trm (ctx :/: tIn))

end

namespace Val

def bindTop {ctx : Ctx} {tIn : Typ} (input : Val) :
    {typ : Typ} -> ProxyTop (ctx :/: tIn) typ -> Val
  | _, .ptop => input

end Val

namespace Trm

/--
Evaluates a term by spending one fuel at each semantic descent.

Runtime reference resolution is injected only as an argument to this evaluator.
-/
def eval {ctx : Ctx} (self : Trm ctx)
    (env : {typ : Typ} -> ProxyTop ctx typ -> Val) : RecOption Val
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield (some value)
    | .apply fn arg =>
      match eval fn env fuel, eval arg env fuel with
      | .yield (some (.fn _tIn body)), .yield (some input) =>
        eval (body .ptop) (Val.bindTop input) fuel
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none
    | .ref top =>
      .yield (some (env top))

end Trm

end AST

end STLC_CE

end Lp2lc.Active
