-- import Std
-- import «Lp2lc».Active.Shared
-- import «Lp2lc».Active.Util
-- import «Lp2lc».Active.STLC.STLCDef

-- namespace Lp2lc.Active

-- namespace STLC
-- open Lp2lc.Active.Util

-- section variable {I : Free}

-- structure TrmIn where
--   self: AST.Trm I
--   fuel: Nat

-- def isSafe -- doesn't use type
--   (trm : TrmIn)
--   -- (typ : AST.Typ I)
-- :=
--   let inferred := trm.self.infer trm.fuel
--   let evaled := trm.self.eval trm.fuel

--   -- evaled.map ( fun v =>

--   -- )
--   -- .getOrElse True
--   sorry
--   -- match evaled with
--   -- | .yields v =>
--   --   let _inferred : (AST.Trm.val v).infer
--   --   _inferred <= inferred
--   -- | .outOfFuel => True

-- -- /--
-- -- trm with a built-in safety proof

-- -- it's the evaluation target of compile function, like value to eval function
-- -- -/
-- -- structure SafeTrm [Compiler.Env I] (I : Free) where
-- --   trm : AST.Trm I
-- --   typ : AST.Typ I
-- --   proof: [Runtime.Env] -> (trm.infer.shouldYields typ) /\   Rec trm.infer.shouldYields typ -- in STLC this is just an equality! extension will happen later

-- -- namespace Proving

-- -- class Env : Type extends Compiler.Env I where
-- --   proofRefs : FBound I.Index (SafeTrm I)

-- -- end Proving

-- -- -- TODO: mimic Trm.recInfer
-- -- def proveSafety [fb: FBound I.Index (SafeTrm I)] (trm: AST.Trm I): RecOption (SafeTrm I)
-- -- | 0 => .outOfFuel
-- -- | _fule + 1 =>
-- --   match trm with
-- --   | .ref k =>
-- --     -- TODO get AdequateTrm I directly from Compiler Env
-- --     let v := fb.load (p := ()) k
-- --     Outcome.yield v
-- --   | .apply left right => -- TODO: application
-- --     let _ll := proveSafety left
-- --     let _rr := proveSafety right
-- --     ll.typ
-- --     sorry
-- --   | .val v =>
-- --     let condition : Condition I := fun _ => True
-- --     let proof : trm.CanSatisfy_semi condition := sorry -- TODO trivial, introduce 1 fuel, run Trm.eval immediately and proof CanSatisfy.
-- --     .mk trm condition proof

-- --     -- argue that _ll must be a function, _rr must be a value of compatible type

-- --     sorry

-- end
-- end STLC

-- end Lp2lc.Active
