import «Lp2lc».Active.STLC.__Infer

namespace Lp2lc.Active.STLC

open Lp2lc.Active.Util

namespace Umbral
section variable {refs} [build : BuildEnv refs] [exe : ExeEnv refs]

 /-
TODO : this use the Safety definition and AST.infer in [__Infer.lean], this is bad.
this file is meant to be self-contained and refer to no other file, [__Infer.lean] should be used as an example, not a reference.

Redefine Safety using [AST.infer] in this file, then replace the reference `Safety trm t2` using the new Safety definition

You may need to inline this structure or convert it into abbreviation, and/or add mutual block to avoid forward reference

do not write duplicated code, or make it much longer
-/
structure TypeWithSafey
    (trm : AST.Trm refs.ExeParameters) where
  t2 : AST.Typ build.BuildParameters
  safety : [_exe : ExeEnv refs] -> Safety trm t2

/-
This is an agumented version of [AST.Trm.infer].

There is only 1 difference: it must produce a type judge with safety proof that trm always evaluate to a value of the same type

It also has access to [ProvingEnv], a mirror of [BuildEnv] with [uid2typWithSafetyCtx] : an extra equivalence between type with safety proof and a subtype of UId

TODO: discharge this function.
- The execution of `Trm.infer` should yield identical `TypeWithSafey.t2` without safety proof
- If the original `Trm.infer` is unsafe, revise it to be safe first
- You are allowed to add more context into ProvingEnv namespace to meet proving demand
-/
/-- Infers build types for executable terms. -/
def AST.infer
    (trm : AST.Trm refs.ExeParameters) :
    RecOpt (TypeWithSafey trm) := sorry


def uid2typWithSafetyCtx := -- TODO: make it forward-referrable by infer
    build.uid2typCtx.mkLesser
      (λ _v => PSigma (λ (trm : ∀ {B : UIdU}, AST.Trm { F := refs.uid2val.UId, B := B, D := refs.D }) =>
        TypeWithSafey trm))

end
end Umbral

end Lp2lc.Active.STLC
