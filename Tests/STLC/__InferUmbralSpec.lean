import «Lp2lc».Active.STLC.__Infer_umbral
import «Tests».STLC.TrmDemo

namespace Tests.STLC.InferUmbralSpec

open Lp2lc.Active.Util
open Lp2lc.Active.Util.Rec
open Lp2lc.Active.STLC

section objectiveResultMismatch

open Tests.STLC.Sanity.Symbolic
open Tests.STLC.Sanity.Trm

example [env : @Umbral.ProvingEnv I] :
    Umbral.infer_prove primitiveTrueFnOnFalse 3 = .yield none ∧
      primitiveTrueFnOnFalse.infer 3 = .yield (some .primitive) := by
  constructor
  · rfl
  · have hPrimitive : (AST.primitive : Typ) ≤ .primitive := by
      rfl
    simp [AST.infer, Outcome.map, primitiveTrueFnOnFalse, primitiveTrueFn, vFalse,
      hPrimitive]

end objectiveResultMismatch

section aux0SafetyContextCollapse

variable {F : Free} [env : @ProvingBase F]
variable [safetyCtx : UIDEquiv.Aux0 env.trm2typCtx
  (λ trm2typ => Safety trm2typ.trm trm2typ.typ)]

example (trm2typ : AST.Trm2Typ F) :
    Safety trm2typ.trm trm2typ.typ := by
  have result := safetyCtx.invEv (env.trm2typCtx.getUID trm2typ)
  simpa using result

example (repr : F.Data) : False := by
  have notSafe :
      ¬ Safety
        (.apply (.val (.lit repr)) (.val (.lit repr)))
        .primitive := by
    intro safety
    unfold Safety at safety
    specialize safety 2
    simp [AST.eval] at safety
  apply notSafe
  have result := safetyCtx.invEv
    (env.trm2typCtx.getUID
      ⟨.apply (.val (.lit repr)) (.val (.lit repr)), .primitive⟩)
  simpa using result

end aux0SafetyContextCollapse

end Tests.STLC.InferUmbralSpec
