import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

/--
Adds the compile-time typing context; the shared value-or-type view permits
only lookups, so compile-time code cannot mint receipts from new values.
-/
class BuildEnv (refs : HasUId2Any) where
  uid2typ : refs.uid2any.Lesser refs.UId (AST.Typ refs.Parameters)
  uid2typCtx : KVEquiv uid2typ.toKVRefs -- comparing to ExeEnv, it lose the ability to save value but gain the ability to save type

namespace BuildEnv
section variable {refs : HasUId2Any} (self : BuildEnv refs)

end
end BuildEnv

namespace AST

/--
Infers types from the shared value-or-type reference view.

Value references are inferred recursively, while type references are returned
directly. Compile-time code can read both payloads but can mint only type
receipts through [BuildEnv.uid2typCtx].

WARNING: this function should have no access to ExeEnv! Executing in compile time is strictly prohibited
-/
def infer {refs : HasUId2Any} [env : BuildEnv refs]
    (self : Trm refs.Parameters) : RecOpt (Typ refs.Parameters)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value =>
      match value with
      | .lit _ => .yield (some .primitive)
      | .lam body tIn =>
        let receipt := env.uid2typCtx.inv tIn
        ((body.apply receipt).infer fuel).map
          (λ out => out.map (λ tOut => .fn tIn tOut))
    | .apply fnTerm arg =>
      let anf := (infer fnTerm fuel, infer arg fuel)
      match anf with
      | (.yield (some (.fn tIn tOut)), .yield (some argTyp)) =>
        if argTyp ≤ tIn then .yield (some tOut) else .yield none
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .yield none
    | .ref receipt =>
      match refs.uid2any.get receipt with
      | .inl value => value.asTrm.infer fuel
      | .inr typ => .yield (some typ)

-- TODO: remove, not useful
def CanInhabit {refs : HasUId2Any} [env : BuildEnv refs]
    (trm : Trm refs.Parameters) (t2 : Typ refs.Parameters) : Prop :=
  trm.infer.isDecidable (λ t1 => t1 ≤ t2)

end AST

def Safety {refs : HasUId2Any} [build : BuildEnv refs] [exe : ExeEnv refs]
    (trm : AST.Trm (ExeEnv.Parameters exe)) (t2 : AST.Typ refs.Parameters) : Prop :=
  trm.eval.isSemiDecidable
    (λ v =>
      (AST.Val.asTrm (AST.recarrier (Q := refs.Parameters) v exe.uid2val.upcastK.toFun id)).infer.isDecidable
        (λ t1 => t1 ≤ t2))

end Lp2lc.Active.STLC
