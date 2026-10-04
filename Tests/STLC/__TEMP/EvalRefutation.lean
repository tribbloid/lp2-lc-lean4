import «Lp2lc».Active.STLC.Serial.Eval
import «Tests».STLC.TrmDemo

namespace Tests.STLC.EvalRefutation

open Lp2lc.Active.STLC Lp2lc.Active.Util
open Tests.STLC.Sanity
open Lp2lc.Active.Util.Indices.SerialProxy (only)

section eval

private def outerValue : RuntimeValue := .mk 0 (.lit "outer") (λ _ => none)

private def hostileBindings : Nat → Option RuntimeValue := λ _ => some outerValue

private def boundIdentity : RuntimeValue :=
  .mk 0 (.fn .TLit (.mk (λ input => .ref input .same))) hostileBindings

private def boundCapture : RuntimeValue :=
  .mk 0 (.fn .TLit (.mk (λ _ =>
    .ref only (.lower (.lower .same))))) hostileBindings

private def boundGhost : RuntimeValue :=
  .mk 0 (.fn .TLit (.mk (λ _ =>
    .ref only (.lower .same)))) hostileBindings

private def boundApply : Trm 0 :=
  .apply (.ref only .same) Trm.vFalse

example : AST.eval boundApply (λ _ => some boundIdentity) 2 =
    AST.eval boundApply (λ _ => some boundIdentity) 7 := rfl
example : AST.eval boundApply (λ _ => some boundCapture) 2 =
    AST.eval boundApply (λ _ => some boundCapture) 7 := rfl
example : AST.eval boundApply (λ _ => some boundGhost) 2 = .yield none := rfl
example : AST.eval boundApply (λ _ => some boundGhost) 7 = .yield none := rfl
example : AST.eval boundApply (λ _ => none) 2 = .yield none := rfl
example : AST.eval boundApply (λ _ => none) 7 = .yield none := rfl
example : AST.eval Trm.get1stOnTuple hostileBindings 3 =
    AST.eval Trm.get1stOnTuple hostileBindings 7 := rfl
example : AST.eval Trm.get2ndOnTuple hostileBindings 3 =
    AST.eval Trm.get2ndOnTuple hostileBindings 7 := rfl
example : AST.eval Trm.Malformed.idFnOnFalse2 hostileBindings 3 =
    AST.eval Trm.Malformed.idFnOnFalse2 hostileBindings 7 := rfl
example : AST.eval (.apply Trm.vFalse Trm.primitiveIdFnOnFalse) hostileBindings 2 = .outOfFuel := rfl
example : AST.eval (.apply Trm.vFalse Trm.primitiveIdFnOnFalse) hostileBindings 3 = .yield none := rfl
example : AST.eval (.apply Trm.vFalse Trm.primitiveIdFnOnFalse) hostileBindings 7 = .yield none := rfl

end eval

end Tests.STLC.EvalRefutation
