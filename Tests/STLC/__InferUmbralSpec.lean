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

end Tests.STLC.InferUmbralSpec
