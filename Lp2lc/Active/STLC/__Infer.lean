import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

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
      ((body index).infer_core fuel).map
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

/-- Combines the executable and build-time environments, equating their value bridges. -/
class ProvingBase extends ExeEnv, BuildEnv where
  trm2valAgree : trm2valCtx.toUIdView = trm2val

namespace ProvingBase

theorem trm2valUIdAgree (env : ProvingBase) : env.trm2valCtx.UId = env.trm2val.UId := by
  rw [env.trm2valAgree]

/-- Transports executable terms onto the build-time carrier along the bridged value view. -/
instance trm2valCoe [env : ProvingBase] : Coe (AST.Trm env.ExeParameters) (AST.Trm env.toBuildEnv.ExeParameters) where
  coe trm := trm.map (F := env.ExeParameters) (G := env.toBuildEnv.ExeParameters)
    (λ c => cast (env.trm2valUIdAgree) c) id

end ProvingBase

def Safety [env : ProvingBase]
    (trm : AST.Trm env.ExeParameters) (t2 : AST.Typ env.BuildParameters) : Prop :=
  trm.eval.isSemiDecidable
    (λ v => v.asTrm.infer.isDecidable (λ t1 => t1 ≤ t2))


/-
safety condition given only a term

comparing to the safety condition in [__Infer.lean], it is much shorter & has less arguments
-/
def Fundamental [env : ProvingBase]
    (trm : AST.Trm env.ExeParameters) : Prop :=
  trm.infer.isSemiDecidable (
    λ t1 =>
      Safety trm t1
  )

end Lp2lc.Active.STLC
