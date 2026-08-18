import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

namespace AST


/-- Infers build types for executable terms. -/
def infer [env : BuildEnv]
    (self : Trm env.ExeParameters) : RecOpt (Typ env.BuildParameters) := sorry

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

class ProvingBase extends BuildEnv

def Safety [env : ProvingBase]
    (trm : AST.Trm env.ExeParameters) (t2 : AST.Typ env.BuildParameters) : Prop :=
  trm.eval.isSemiDecidable
    (λ v => v.asTrm.infer.isDecidable (λ t2 => t2 ≤ t2))


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
