import «Lp2lc».Next.STLC.STLCDef

namespace Lp2lc.Next.STLC

open Lp2lc.Active.Util

namespace AST

/-- Infers build types for executable terms, recursively resolving runtime references. -/
def infer [env : BuildEnv]
    (self : Trm env.BuildF) : RecOpt (Typ env.BuildF)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val (.lit _) => .yield (some .primitive)
    | .val (.lam body tIn) =>
      let index : env.BuildF.Carrier := .inr (env.trm2typCtx.inv (.lam body tIn))
      (infer (body index) fuel).map
        (λ out => out.map (λ tOut => .fn tIn tOut))
    | .apply fnTerm arg =>
      match infer fnTerm fuel, infer arg fuel with
      | .yield (some (.fn tIn tOut)), .yield (some argTyp) =>
        if argTyp ≤ tIn then .yield (some tOut) else .yield none
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none
    | .ref (.inl receipt) =>
      let original : Val env.BuildF := mapCarrier (Sum.inl) (env.trm2valCtx.get receipt)
      original.asTrm.infer fuel
    | .ref (.inr receipt) =>
      match env.trm2typCtx.get receipt with
      | .lit _ => .yield (some .primitive)
      | .lam _ tIn => .yield (some tIn)

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
    (self : Trm env.BuildF) (typ : Typ env.BuildF) : Prop :=
  self.infer.isDecidable (λ inferred => inferred ≤ typ)

end AST

class ProvingBase extends BuildEnv

def Safety [env : ProvingBase]
    (trm : AST.Trm env.ExeF) (typ : AST.Typ env.BuildF) : Prop :=
  trm.eval.isSemiDecidable
    (λ value => (AST.mapCarrier (Sum.inl) value.asTrm).CanInhabit typ)

end Lp2lc.Next.STLC
