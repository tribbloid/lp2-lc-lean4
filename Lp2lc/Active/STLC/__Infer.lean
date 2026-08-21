import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

/--
Adds the compile-time typing context; its value view only permits lookups,
so compile-time code cannot mint receipts from new values.
-/
class BuildEnv extends HasData where
  trm2val : UIdView (λ T => AST.Val { C := T, D := D })
  mkUId4Typ : CanMkUIdFor (λ T =>
    let TC := trm2val.UId ⊕ T
    AST.Typ { C := TC, D := D })

namespace BuildEnv
section variable (env : BuildEnv)

abbrev trm2typCtx : Fixpoint (λ T =>
  let TC := env.trm2val.UId ⊕ T
  AST.Typ { C := TC, D := env.D }) := env.mkUId4Typ.mkEquiv

abbrev ExeParameters : Parameters :=
  { C := env.trm2val.UId, D := env.D }

abbrev BuildParameters : Parameters :=
  { C := env.trm2val.UId ⊕ env.trm2typCtx.UId, D := env.D }

end
end BuildEnv

namespace AST

/-- Infers build types for executable terms, recursively resolving runtime references. -/
def infer_core [env : BuildEnv]
    (self : Trm env.BuildParameters) : RecOpt (Typ env.BuildParameters)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val (.lit _) => .yield (some .primitive)
    | .val (.lam body tIn) =>
      let index : env.BuildParameters.C := .inr (env.trm2typCtx.inv tIn)
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
        (env.trm2val.get receipt).map (F := env.ExeParameters) (G := env.BuildParameters) (Sum.inl) id
      original.asTrm.infer_core fuel
    | .ref (.inr receipt) =>
      .yield (some (env.trm2typCtx.get receipt))

/-- Infers build types for executable terms. -/
def infer [env : BuildEnv]
    (self : Trm env.ExeParameters) : RecOpt (Typ env.BuildParameters) :=
    let upcasted := self.map (F := env.ExeParameters) (G := env.BuildParameters) (Sum.inl) id
    infer_core upcasted

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

def CanInhabit [env : BuildEnv]
    (self : Trm env.BuildParameters) (typ : Typ env.BuildParameters) : Prop :=
  self.infer_core.isDecidable (λ inferred => inferred ≤ typ)

end AST

private theorem castUIdViewUId {left right : HasData} (h : left = right)
    (view : UIdView (λ T => AST.Val { toHasData := left, C := T })) :
    (h ▸ view).UId = view.UId := by
  cases h
  rfl

class CompatExeEnv (build : BuildEnv) extends ExeEnv where
  hD : toExeEnv.toHasData = build.toHasData
  hTrm2val : build.trm2val = hD ▸ (toExeEnv.trm2valCtx).toUIdView

def Safety [build : BuildEnv] [env : CompatExeEnv build]
    (trm : AST.Trm env.ExeParameters) (t2 : AST.Typ build.BuildParameters) : Prop :=
  trm.eval.isSemiDecidable
    (λ v => v.asTrm.infer.isDecidable (λ t1 => t1 ≤ t2))


/-
-- TODO: this is the "Paranoid Fundamental theorem": compilation may fail even but term evaluation may succeed.
-- TODO: enable later
-/
-- /--
-- if compiled a term and succeeded, the term must be safe
-- -/
-- def Fundamental [env : ProvingBase]
--     (trm : AST.Trm env.ExeParameters) : Prop :=
--   trm.infer.isSemiDecidable (
--     λ t1 =>
--       Safety trm t1
--   )

end Lp2lc.Active.STLC
