import Std
import «Lp2lc».Active.Shared
import «Lp2lc».Active.STLC.__Infer

namespace Lp2lc.Active

namespace STLC
open Lp2lc.Active.Util

section variable {F : Free}

namespace UmbralV2
section variable [@ProvingBase F]

structure ProvenCondition (trm: AST.Trm F) : Type where
  typ : AST.Typ F
  safety: Safety trm typ

class ProvingEnv where
  base: @ProvingBase F
  safetyCtx : base.trm2typCtx.Aux (λ trm2typ =>
    Safety trm2typ.trm trm2typ.typ)

/--
the objective of infer_proveV2 contains 2 parts:
- recursive algorithm that may produce one of the 3 consequences:
  - successful result
  - error
  - out-of-fuel
- in **all 3** consequences, the algorithm must yield the same result as trm.infer
-/
structure ProvingObjective (trm: AST.Trm F) where
  proving : RecOption (ProvenCondition trm)
  sameResult: ∀ (fuel : Nat),
    (proving fuel).map (λ result => result.map (λ condition => condition.typ)) =
      trm.infer fuel

def infer_prove [env: @ProvingEnv F] (trm : AST.Trm F) : ProvingObjective trm := sorry

end
end UmbralV2

namespace Umbral

section variable [@ProvingBase F]

structure ProvenCondition (trm2typ: AST.Trm2Typ F) : Type where
  sameInfer: trm2typ.trm.infer.isDecidable (λ t2 => trm2typ.typ <= t2)
  safety: Safety trm2typ.trm trm2typ.typ

end

/--
contains a [UIDEquiv.Aux] store for intermediate safety proofs over both `AST.Trm` and `AST.Val`

`infer_prove` & any theorem that relies on safety can use it, this is the only correspondence between compiletime and runtime variables.
-/
class ProvingEnv where
  [base: @ProvingBase F]

namespace ProvingEnv

/-- Canonical proof store derived from `base`, fixed for every `ProvingEnv` instance. -/
@[reducible]
def proofCtx (env : @ProvingEnv F) :
    env.base.trm2typCtx.Aux (λ t => @ProvenCondition F env.base t) :=
  env.base.mkAux env.base.trm2typCtx (λ t => @ProvenCondition F env.base t)

end ProvingEnv

instance [env: @ProvingEnv F] : @ProvingBase F := env.base

section variable [@ProvingEnv F]

/--
like `Trm.infer` it inductively infer `Typ` of a given `Trm`, using the structure of `Trm.infer` as a blueprint.

unlike `Trm.infer` it is obliged to produce a `ProvenCondition` bundle of:

- original `Typ`
- proof that it has the same result to `Trm.infer`
- proof that the `Trm : Typ` pair is safe to evaluate
-/
def infer_prove [env: @ProvingEnv F] (trm : AST.Trm F) :
    RecOption (PSigma (λ typ : AST.Typ F => @ProvenCondition F env.base ⟨trm, typ⟩)) :=
  λ
  | 0 => .outOfFuel
  | fuel + 1 =>
    let proven (term : AST.Trm F) (typ : AST.Typ F) :
        Option (@ProvenCondition F env.base ⟨term, typ⟩) :=
      let id := env.base.trm2typCtx.getUID ⟨term, typ⟩
      (env.proofCtx.lookup id).map (λ member => by
        simpa [id] using env.proofCtx.invEv ⟨id, member.down⟩)
    match trm with
    | .val (.primitive repr) =>
      .yield ((proven (.val (.primitive repr)) .primitive).map
        (λ condition => ⟨.primitive, condition⟩))
    | .val (.fn body tIn) =>
      let index := env.base.trm2typCtx.getUID ⟨trm, tIn⟩
      ((infer_prove (body index)) fuel).map (λ out =>
        out.bind (λ result =>
          (proven (.val (.fn body tIn)) (.fn tIn result.fst)).map
            (λ condition => ⟨.fn tIn result.fst, condition⟩)))
    | .apply fn arg =>
      match (infer_prove fn) fuel, (infer_prove arg) fuel with
      | .yield (some ⟨.fn tIn tOut, _⟩), .yield (some ⟨argTyp, _⟩) =>
        if argTyp ≤ tIn then
          .yield ((proven (.apply fn arg) tOut).map
            (λ condition => ⟨tOut, condition⟩))
        else .yield none
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none
    | @AST.Trm.ref _ i =>
      let typ := (env.base.trm2typCtx.inv i).typ
      .yield ((proven (.ref i) typ).map
        (λ condition => ⟨typ, condition⟩))

end

end Umbral

namespace UmbralV3

section variable [@ProvingBase F]

/-- A proof-producing inference computation with the same complete outcome as `Trm.infer`. -/
structure ProvenCondition (trm : AST.Trm F) : Type where
  result : RecOption (AST.Typ F)
  sameResult : result = trm.infer
  safety : result.isSemiDecidable (λ typ => Safety trm typ)

class ProvingEnv where
  [base: @ProvingBase F]

namespace ProvingEnv

/-- Canonical proof store derived from `base`, fixed for every `ProvingEnv` instance. -/
@[reducible]
def proofCtx (env : @ProvingEnv F) :
    env.base.trm2typCtx.Aux (λ t => @ProvenCondition F env.base t.trm) :=
  env.base.mkAux env.base.trm2typCtx (λ t => @ProvenCondition F env.base t.trm)

end ProvingEnv

namespace Proven
section variable [env : @ProvingEnv F]

def FProven : Free :=
  {
    Index := PSigma env.proofCtx.Ev
    Data := F.Data
  }

end
end Proven

end

/-
Hitting the new wall: new UID + proof-evidence can't be saved into AST, and won't be available during induction

How to save proof-evidence into AST? either using the same UID + extrinsic store, or PHO-AST migrated to a new carrier?

can the "leftover case" in AST definition help?

## What we have:

- (x : Trm ⟨ I, ⟩).eval
- (x : Trm ⟨ I, ⟩).infer

## What we want:

- (x : Trm.ref (Ev I)), which carries an evidence of safety

## Possible solution:

- explicitly define generic constructors of Fixpoint & Aux, all instances have to use them
- after getting a `Ev I`, instead of creating `.ref <I, >`, create `.ref <Ev I, >` instead
- enable conversion from Trm (Ev I) (representing safe term) to Trm I (representing unsafe term)

The annoying part is that AST.Trm <I> is invariant to I (`I` appear in both + / - positions), it has to be broken

-/

end UmbralV3

end

end STLC
