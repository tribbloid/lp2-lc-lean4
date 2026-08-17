import «Lp2lc».Next.STLC.STLCDef

namespace Lp2lc.Next.STLC

open Lp2lc.Active.Util

namespace AST

/-- Evaluates terms whose references carry receipts from the runtime context. -/
def eval [env : ExeEnv] -- TODO: should move to STLCDef.lean
    (self : Trm env.ExeF) : RecOpt (Val env.ExeF)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield (some value)
    | .apply fnTerm arg =>
      let anf := (eval fnTerm fuel, eval arg fuel)
      match anf with
      | (.yield (some (.lam body _tIn)), .yield (some input)) =>
        let receipt := env.trm2valCtx.inv input
        eval (body receipt) fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .yield none
    | .ref receipt =>
      .yield (some (env.trm2valCtx.get receipt))

-- TODO: the following section should be in __Infer.lean

/-- Infers build types for executable terms, recursively resolving runtime references. -/
def infer [env : BuildEnv]
    (self : Trm env.ExeF) : RecOpt (Typ env.BuildF)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val (.lit _) => .yield (some .primitive)
    | .val (.lam body tIn) =>
      let cIn : Typ env.BuildF := Typ.recarrier tIn
      let index : env.ExeF.Carrier := by sorry
      (infer (body index) fuel).map
        (λ out => out.map (λ tOut => .fn cIn tOut))
    | .apply fnTerm arg =>
      match infer fnTerm fuel, infer arg fuel with
      | .yield (some (.fn tIn tOut)), .yield (some argTyp) =>
        if argTyp ≤ tIn then .yield (some tOut) else .yield none
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none
    | .ref receipt =>
      let original := env.trm2valCtx.get receipt
      original.asTrm.infer fuel

/-
TODO: GPT is right:

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
    (self : Trm env.ExeF) (typ : Typ env.BuildF) : Prop :=
  self.infer.isDecidable (λ inferred => inferred ≤ typ)

end AST

class ProvingBase extends BuildEnv

def Safety [env : ProvingBase]
    (trm : AST.Trm env.ExeF) (typ : AST.Typ env.BuildF) : Prop :=
  trm.eval.isSemiDecidable (λ value => value.asTrm.CanInhabit typ)

-- TODO: Umbral namespace should be in __Infer_Umbral.lean

namespace Umbral

section variable [env : ProvingBase]

structure SafetyOf (trm : AST.Trm env.ExeF) where
  typ : AST.Typ env.BuildF
  -- safety : Safety trm typ -- TODO: this lemma has been temporarily disabled. Enable it later.

abbrev Compilation (trm : AST.Trm env.ExeF) :=
  Rec.OutcomeOpt (SafetyOf trm) -- one observation of the semi-decidability of executing term

/-- Requires the proving computation to shadow term inference at the selected fuel. -/
structure Objective (trm : AST.Trm env.ExeF) (fuel : Nat) : Type where
  compilation : Compilation trm
  sameInfer : compilation.map (Option.map SafetyOf.typ) = trm.infer fuel

end

end Umbral

end Lp2lc.Next.STLC
