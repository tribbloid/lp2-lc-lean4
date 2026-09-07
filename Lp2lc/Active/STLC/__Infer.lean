import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

/--
Adds the compile-time typing context; the shared value-or-type view permits
only lookups, so compile-time code cannot mint receipts from new values.
-/
class BuildEnv (refs : EverythingRefs) where
  uid2typCtx : UIdEquiv.Lesser (base := refs.uid2any)
    ⟨Sum.inr, λ _left _right => Sum.inr.inj⟩

namespace BuildEnv
section variable {refs : EverythingRefs} (self : BuildEnv refs)

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
def infer {refs} [env : BuildEnv refs]
    (self : Trm refs.Parameters) : RecOpt (Typ refs.Parameters)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value =>
      match value with
      | .lit _ => .yield (some .primitive)
      | .lam body tIn =>
        let receipt := env.uid2typCtx.inv tIn
        ((body receipt.val).infer fuel).map
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
def CanInhabit {refs} [env : BuildEnv refs]
    (trm : Trm refs.Parameters) (t2 : Typ refs.Parameters) : Prop :=
  trm.infer.isDecidable (λ t1 => t1 ≤ t2)

end AST

def Safety {refs : EverythingRefs} [build : BuildEnv refs] [exe : ExeEnv refs]
    (trm : AST.Trm refs.Parameters) (t2 : AST.Typ refs.Parameters) : Prop :=
  trm.eval.isSemiDecidable
    (λ v => v.asTrm.infer.isDecidable (λ t1 => t1 ≤ t2))

end Lp2lc.Active.STLC
