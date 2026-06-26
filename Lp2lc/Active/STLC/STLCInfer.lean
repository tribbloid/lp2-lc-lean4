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


class ProvingEnv extends (@RuntimeEnv I), (@CompilerEnv I) where


-- structure TrmIn where
--   self: AST.Trm I
--   fuel: Nat

-- def isSafe -- doesn't use type
--   [env : Proving.Env I]
--   (trm : TrmIn I)
--   -- (typ : AST.Typ I)
--   : Prop
-- :=
--   let t1 := AST.Trm.infer (I := I) (env := compilerEnv) trm.self trm.fuel
--   let evaled := AST.Trm.eval (I := I) (env := runtimeEnv) trm.self trm.fuel

--   evaled.map ( fun v =>
--     let t2 := v.infer (env := compilerEnv)
--     t2 <= t1
--   )
--   .getOrElse False
  -- .getOrElse True
  -- match evaled with
  -- | .yields v =>
  --   let _inferred : (AST.Trm.val v).infer
  --   _inferred <= inferred
  -- | .outOfFuel => True
  -- sorry

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
