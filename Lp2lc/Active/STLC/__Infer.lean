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
section variable (self : BuildEnv)

abbrev trm2typCtx : Fixpoint (λ T =>
  let TC := self.trm2val.UId ⊕ T
  AST.Typ { C := TC, D := self.D }) := self.mkUId4Typ.mkEquiv

abbrev BuildParameters : Parameters :=
  { C := self.trm2val.UId ⊕ self.trm2typCtx.UId, D := self.D }

end
end BuildEnv

namespace AST

/--
Infers build types for executable terms, recursively resolving runtime references.

WARNING: this function should have no access to ExeEnv! Executing in compile time is strictly prohibited
-/
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
        (env.trm2val.get receipt).map Sum.inl id
      original.asTrm.infer_core fuel
    | .ref (.inr receipt) =>
      .yield (some (env.trm2typCtx.get receipt))

/-- Infers build types for executable terms. -/
def infer [env : BuildEnv]
    (self : Trm env.ExeParameters) : RecOpt (Typ env.BuildParameters) :=
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

def CanInhabit [env : BuildEnv]
    (self : Trm env.BuildParameters) (typ : Typ env.BuildParameters) : Prop :=
  self.infer_core.isDecidable (λ inferred => inferred ≤ typ)

end AST

private theorem castUIdViewUId {left right : HasData} (h : left = right)
    (view : UIdView (λ T => AST.Val { toHasData := left, C := T })) :
    (h ▸ view).UId = view.UId := by
  cases h
  rfl

/-
TODO: this definition is transport hell, can it be shortened?
-/
class CompatExeEnv (build : BuildEnv) extends ExeEnv where
  hD : toExeEnv.toHasData = build.toHasData
  hTrm2val : build.trm2val = hD ▸ (toExeEnv.trm2valCtx).toUIdView

namespace CompatExeEnv

/-- Equates the runtime and build-time receipt carriers. -/
theorem trm2valUIdAgree [build : BuildEnv] (exe : CompatExeEnv build) :
    exe.trm2valCtx.UId = build.trm2val.UId := by
  calc
    _ = (exe.hD ▸ exe.trm2valCtx.toUIdView).UId :=
      (castUIdViewUId exe.hD _).symm
    _ = _ := (congrArg (λ view => view.UId) exe.hTrm2val).symm

/-- Transports executable terms to the compatible build-time carrier. -/
instance trm2valCoe [build : BuildEnv] [exe : CompatExeEnv build] :
    Coe (AST.Trm exe.ExeParameters) (AST.Trm build.ExeParameters) where
  coe trm := trm.map (cast exe.trm2valUIdAgree)
    (cast (congrArg (λ source : HasData => source.D) exe.hD))

end CompatExeEnv

def Safety [build : BuildEnv] [exe : CompatExeEnv build]
    (trm : AST.Trm exe.ExeParameters) (t2 : AST.Typ build.BuildParameters) : Prop :=
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
