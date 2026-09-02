import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

/--
Adds the compile-time typing context; its value view only permits lookups,
so compile-time code cannot mint receipts from new values.
-/
class BuildEnv (refs : TypOrValRefs) where
  uid2typ : refs.uid2either.Lesser (λ v : AST.Typ P => .inr v)
  uid2typCtx : UIdEquiv.Lesser (base := refs.uid2typ) -- can save type to get UId with Ev

namespace BuildEnv
section variable {refs : TypOrValRefs} (self : BuildEnv refs)

end
end BuildEnv

namespace AST

/-- Rebuilds syntax while classifying source binders as target free or bound references. -/
@[simp]
private def recarrier {P Q : Parameters} {l : Label} (self : AST P l)
    (mF : P.F → Q.F) (mB : P.B → Q.F ⊕ Q.B) (mD : P.D → Q.D) : AST Q l :=
  match self with
  | .primitive => .primitive
  | .fn tIn tOut => .fn (tIn.recarrier mF mB mD) (tOut.recarrier mF mB mD)
  | .val value => .val (value.recarrier mF mB mD)
  | .apply fnTerm arg => .apply (fnTerm.recarrier mF mB mD) (arg.recarrier mF mB mD)
  | .ref (.inl free) => .ref (.inl (mF free))
  | .ref (.inr bound) => .ref (mB bound)
  | .lit repr => .lit (mD repr)
  | .lam body tIn =>
    .lam
      (λ {B} lift arg =>
        let sourceLift : P.B → Q.F ⊕ B :=
          λ bound =>
            match mB bound with
            | .inl free => .inl free
            | .inr outer => .inr (lift outer)
        (body (B := Q.F ⊕ B) sourceLift (.inr arg)).recarrier mF id mD)
      (tIn.recarrier mF mB mD)

/--
converting an executable term AST (with only references to value) to a compilable term AST (free variable references to value, bounded variable references to type)

rule-of-thumb: every variable reference in the input AST is automatically lifted into a free variable reference.

as a result, this conversion is fairly universal and doesn't require the term to be closed.
  In fact, it even works if the term is a debugging expression at a breakpoint in the middle of execution.
-/
def exe2build {refs} [env : BuildEnv refs]
    (trm : Trm refs.ExeParameters) : Trm env.BuildParameters :=
  trm.recarrier id Sum.inl id

/--
Infers build types for executable terms, recursively resolving runtime references.

Free references are resolved by instantiating the stored value polymorphism
directly at [BuildEnv.uid2typ]'s carrier; bound references are read through
[BuildEnv.uid2typ].

WARNING: this function should have no access to ExeEnv! Executing in compile time is strictly prohibited
-/
def inferCore {refs} [env : BuildEnv refs]
    (self : Trm env.BuildParameters) : RecOpt (Typ env.BuildParameters)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val (.lit _) => .yield (some .primitive)
    | .val (.lam body tIn) =>
      let index : env.BuildParameters.B := env.uid2typCtx.inv tIn
      ((body id index).inferCore fuel).map
        (λ out => out.map (λ tOut => .fn tIn tOut))
    | .apply fnTerm arg =>
      match inferCore fnTerm fuel, inferCore arg fuel with
      | .yield (some (.fn tIn tOut)), .yield (some argTyp) =>
        if argTyp ≤ tIn then .yield (some tOut) else .yield none
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none
    | .ref (.inl free) =>
      let exeTrm : Trm refs.ExeParameters := (refs.uid2val.get free).asTrm
      let buildTrm := exeTrm.exe2build
      buildTrm.inferCore fuel
    | .ref (.inr bounded) =>
      .yield (some (env.uid2typ.get bounded))


def infer {refs} [env : BuildEnv refs]
    (self : Trm refs.ExeParameters) : RecOpt (Typ env.BuildParameters) :=
    self.exe2build.inferCore

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

def Safety {refs : TypOrValRefs} [build : BuildEnv refs] [exe : ExeEnv refs]
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
def Fundamental {refs : TypOrValRefs} [build : BuildEnv refs] [exe : ExeEnv refs]
    (trm : AST.Trm refs.ExeParameters) : Prop :=
  trm.infer.isSemiDecidable (
    λ t1 =>
      Safety trm t1
  )

end Lp2lc.Active.STLC
