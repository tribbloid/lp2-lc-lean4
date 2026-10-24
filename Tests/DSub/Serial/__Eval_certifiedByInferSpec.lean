import «Lp2lc».Active.DSub.Serial.__Eval_certifiedByInfer

namespace Tests.DSub.EvalCertifiedByInferSpec

open Lp2lc.Active.DSub Lp2lc.Active.Util

section eval_certified

private def erasedEval (trm : Trm) : RecOpt (Return ExeVal) :=
  match hInfer : trm.infer .empty 32 with
  | .yield (some _) => λ fuel =>
      (trm.eval_certified .empty hInfer fuel).map (λ result => some (result.map Subtype.val))
  | .yield none => λ _ => .yield none
  | .outOfFuel => λ _ => .outOfFuel

private def literal : Trm := .val (.lit "ok")
private def identity : Trm := .val (.fn .TLit (.mk (λ value => .val (.ref value .same))))
private def corruptApplication (n : Nat := 0) : Trm n :=
  .apply (.val (.fnPrimitive (.mk (λ _ => .TBot)) .lit)) (.val (.lit "ok"))

private def literalAt (trm : Trm) (fuel : Nat) : Bool :=
  match erasedEval trm fuel with
  | .yield (some (.some ⟨_, .lit repr, _⟩)) => repr == "ok"
  | _ => false

private def corruptsAt (trm : Trm) (fuel : Nat) : Bool :=
  match erasedEval trm fuel, erasedEval trm 64 with
  | .yield (some .corrupted), .yield (some .corrupted) => true
  | _, _ => false

#guard literalAt literal 1
#guard literalAt (.apply identity literal) 8
#guard literalAt (.apply (.val (.fnPrimitive (.mk (λ _ => .TLit)) .lit)) literal) 8
#guard corruptsAt corruptApplication 3
#guard corruptsAt (.apply corruptApplication literal) 4
#guard corruptsAt (.apply identity corruptApplication) 4
#guard corruptsAt (.apply (.val (.fn .TLit (.mk (λ _ => corruptApplication 1)))) literal) 8

#guard
  let primitive : Val := .fnPrimitive (.mk (λ _ => .TLit)) (λ _ => .typeDef (.TSel (.lit "bad")))
  corruptsAt (.apply (.val primitive) literal) 4

#guard match erasedEval corruptApplication 2 with
  | .outOfFuel => true
  | _ => false

#guard match erasedEval (.apply literal literal) 8 with
  | .yield none => true
  | _ => false

end eval_certified

end Tests.DSub.EvalCertifiedByInferSpec
