import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

/--
Adds the compile-time typing context; its value view only permits lookups,
so compile-time code cannot mint receipts from new values.
-/
class BuildEnv (refs : ExeRefs) where
  uid2typ : UIdView (λ T =>
    let TC := refs.uid2val.UId ⊕ T
    AST.Typ { C := TC, D := refs.D })
  uid2typCtx : UIdEquiv.Extendable.{3, 3} uid2typ

namespace BuildEnv
section variable {refs : ExeRefs} (self : BuildEnv refs)

abbrev BuildParameters : Parameters :=
  { C := refs.uid2val.UId ⊕ self.uid2typ.UId, D := refs.D }

end
end BuildEnv

namespace AST

/--
Infers build types for executable terms, recursively resolving runtime references.

WARNING: this function should have no access to ExeEnv! Executing in compile time is strictly prohibited
-/
def infer_core {refs} [env : BuildEnv refs]
    (self : Trm env.BuildParameters) : RecOpt (Typ env.BuildParameters)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val (.lit _) => .yield (some .primitive)
    | .val (.lam body tIn) =>
      let index : env.BuildParameters.C := .inr (env.uid2typCtx.inv tIn)
      ((body (s := ⟨id⟩) index).infer_core fuel).map
        (λ out => out.map (λ tOut => .fn tIn tOut))
    | .apply fnTerm arg =>
      match infer_core fnTerm fuel, infer_core arg fuel with
      | .yield (some (.fn tIn tOut)), .yield (some argTyp) =>
        if argTyp ≤ tIn then .yield (some tOut) else .yield none
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none
    | .ref (.inl receipt) =>
      let original : Val env.BuildParameters :=
        (refs.uid2val.get receipt).map Sum.inl id
      original.asTrm.infer_core fuel
    | .ref (.inr receipt) =>
      .yield (some (env.uid2typ.get receipt))

/-- Infers build types for executable terms. -/
def infer {refs} [env : BuildEnv refs]
    (self : Trm refs.ExeParameters) : RecOpt (Typ env.BuildParameters) :=
  infer_core (self.map Sum.inl id)

/-
DEFER: GPT is right:

- either the carrier have to be shared between type and value (value is a special singleton type)
  - if this happens, BuildEnv context will be an extension of RuntimeEnv, for both type OR value
  - an extra inductive will be defined for type OR value
  - Trm.infer will work on any term! even with free variables
  - It's always just a sanity test, the pie is the umbral proof
  - a new, extendable UIdEquiv definition will be required, with same roundtrip theorem but can extends to supertype
  - is it **THE LAST** extension?
- or AST.ref have to carry the entire UIdEquiv for lookup
-/

-- TODO: remove, not useful
def CanInhabit {refs} [env : BuildEnv refs]
    (trm : Trm refs.ExeParameters) (t2 : Typ env.BuildParameters) : Prop :=
  trm.infer.isDecidable (λ t1 => t1 ≤ t2)

end AST

def Safety {refs : ExeRefs} [build : BuildEnv refs] [exe : ExeEnv refs]
    (trm : AST.Trm refs.ExeParameters) (t2 : AST.Typ build.BuildParameters) : Prop :=
  trm.eval.isSemiDecidable
    (λ v => v.asTrm.infer.isDecidable (λ t1 => t1 ≤ t2))

/-
-- TODO: this is the "Paranoid Fundamental theorem": compilation may fail even but term evaluation may succeed.
-- TODO: prove it later?
-/
/--
if compiled a term and succeeded, the term must be safe
-/
def Fundamental {refs : ExeRefs} [build : BuildEnv refs] [exe : ExeEnv refs]
    (trm : AST.Trm refs.ExeParameters) : Prop :=
  trm.infer.isSemiDecidable (
    λ t1 =>
      Safety trm t1
  )

end Lp2lc.Active.STLC
