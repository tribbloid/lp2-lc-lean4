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

def isSafe [env : @ProvingEnv I]
  (trm : AST.Trm I)
  (typ : AST.Typ I)
  (compilerFuel: Nat)
  (hCanCompile : trm.infer compilerFuel = Outcome.yield (.some typ))
  : Prop := -- TODO: this conjecture shouldn't be too long

  trm.eval.isSemiDecidable ( fun vv =>
    match (AST.Trm.val vv).infer compilerFuel with
    | Outcome.yield (.some t2) => t2 <= typ
    | _ => false
  )

-- /--
-- trm with a built-in safety proof

-- it's the evaluation target of compile function, like value to eval function
-- -/
-- structure SafeTrm [CompilerEnv I] (I : Free) where
--   trm : AST.Trm I
--   typ : AST.Typ I
--   proof: [RuntimeEnv] -> (trm.infer.shouldYields typ) /\   Rec trm.infer.shouldYields typ -- in STLC this is just an equality! extension will happen later

-- -- TODO: mimic Trm.recInfer
-- def proveSafety [fb: FBound I.Index (SafeTrm I)] (trm: AST.Trm I): RecOption (SafeTrm I)
-- | 0 => .outOfFuel
-- | _fule + 1 =>
--   match trm with
--   | .ref k =>
--     -- TODO get AdequateTrm I directly from Compiler Env
--     let v := fb.load (p := ()) k
--     Outcome.yield v
--   | .apply left right => -- TODO: application
--     let _ll := proveSafety left
--     let _rr := proveSafety right
--     ll.typ
--     sorry
--   | .val v =>
--     let condition : Condition I := fun _ => True
--     let proof : trm.CanSatisfy_semi condition := sorry -- TODO trivial, introduce 1 fuel, run Trm.eval immediately and proof CanSatisfy.
--     .mk trm condition proof

--     -- argue that _ll must be a function, _rr must be a value of compatible type

--     sorry

end
end STLC

end Lp2lc.Active
