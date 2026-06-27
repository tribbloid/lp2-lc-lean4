import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.Util
import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active

namespace STLC
open Lp2lc.Active.Util

/-
this file proof an alternative theorem for STLC soundness:

term can be inferred to type using some fuel, evaluating it must leads to either a variable that can be inferred to a lesser type with some (less?) fuel or loop.

Obviously inferring type is not alway available in more complex type system, but it's a good demo for recursive proving
-/

section variable {I : Free}

namespace AST.Trm

/--
get the strongest post type bound (post-condition) of a term, or throw an error
-/
def infer [env: @CompilerEnv I] (self : Trm I) : RecOption (Typ I) -- TODO: remove this, not possible in subtyping
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val (.primitive _) => .yield (some .primitive)
    | .val (.fn body tIn) =>
      let index := env.typRefs.save tIn
      ((body index).infer fuel).map (fun out => out.map (fun tOut => .fn tIn tOut))
    | .apply fn arg =>
      match fn.infer fuel, arg.infer fuel with
      | .yield (some (.fn tIn tOut)), .yield (some argTyp) =>
        if argTyp ≤ tIn then .yield (some tOut) else .yield none
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none
    | .ref i => .yield (some (env.typRefs.load i))

end AST.Trm


class ProvingEnv extends (@RuntimeEnv I), (@CompilerEnv I) where

variable [env : @ProvingEnv I]

def Safety : Prop := -- TODO: this conjecture shouldn't be too long
  ∀ (trm : AST.Trm I) (typ : AST.Typ I) (fuel : Nat),
  ∀ (_: (trm.infer fuel) = Outcome.yield (.some typ)),
  trm.eval.isSemiDecidable ( fun vv =>
    match (AST.Trm.val vv).infer fuel with
    | Outcome.yield (.some t2) => t2 <= typ
    | _ => false
  )

namespace Safety

def proof : @Safety I env := sorry

end Safety

end
end STLC

end Lp2lc.Active
