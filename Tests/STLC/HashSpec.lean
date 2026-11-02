import «Lp2lc».Active.STLC.Hash
import «Lp2lc».Active.STLC.UId.Infra

namespace Tests.STLC.HashSpec

open Lean (Json toJson)
open Lp2lc.Active.Util.IndexEncoding.SerialProxy (only)
open Lp2lc.Active.Util Lp2lc.Active.STLC

section hash

private def sigC (index : Nat) : Json := toJson index
private def sigB (repr : String) : Json := toJson repr
private def sigAny (_index : Nat) : Json := .null

private def capturedRef (useOuter : Bool) : Val 1 :=
  .fn .TLit (.mk (λ proxy =>
    if useOuter then .pure (.ref only (.lower .same))
    else .pure (.ref proxy .same)))

private def idVal : Val 1 :=
  .fn .TLit (.mk (λ proxy => .pure (.ref proxy .same)))

example : astToJson (.pure (.ref only .same) : Trm 0) sigC sigB =
    .arr #["pure", .arr #["ref", toJson (0 : Nat)]] := rfl

example : astToJson (.pure (.ref only .same) : Trm 3) sigC sigB =
    .arr #["pure", .arr #["ref", toJson (3 : Nat)]] := rfl

example : astToJson (.TLit : AST 0 .typ) sigC sigB = "primitive" := rfl

section hash

#guard
  let primitive : Val := .fnPrimitive .TLit .lit
  astToJson primitive sigC sigB == .arr #["primitiveFn", "primitive"] &&
    astBEq primitive (.fnPrimitive .TLit (λ _ => .lit "other") : Val) sigC sigB

end hash

example : astToJson (.TFn .TLit .TLit : AST 0 .typ) sigC sigB =
    .arr #["fn", "primitive", "primitive"] := rfl

example : astToJson (.lit "x" : AST 0 .val) sigC sigB =
    .arr #["lit", toJson ("x" : String)] := rfl

example : astToJson idVal sigC sigB =
    .arr #["lam", .arr #["pure", .arr #["ref", toJson (2 : Nat)]], "primitive"] := rfl

example : astToJson (.pure (.val (.lit "x")) : AST 0 .trm) sigC sigB =
    .arr #["pure", .arr #["val", .arr #["lit", toJson ("x" : String)]]] := rfl

example : astToJson (.apply (.pure (.val (capturedRef true))) (.pure (.val (capturedRef false))) : Trm 1) sigC sigB =
    .arr #["apply", .arr #["pure", .arr #["val", .arr #["lam", .arr #["pure", .arr #["ref", toJson (1 : Nat)]], "primitive"]]],
      .arr #["pure", .arr #["val", .arr #["lam", .arr #["pure", .arr #["ref", toJson (2 : Nat)]], "primitive"]]]] := rfl

example : (astToJson (capturedRef true) sigC sigB == astToJson (capturedRef false) sigC sigB) = false :=
  by native_decide

example : astBEq (capturedRef true) (capturedRef false) sigC sigB = false := by native_decide

example : astBEq (capturedRef true) (capturedRef false) sigAny sigB = true := by native_decide

example : astHash (capturedRef true) sigAny sigB = astHash (capturedRef false) sigAny sigB := rfl

example : hashSum (.inl idVal) sigC sigB = astHash idVal sigC sigB := rfl

example : hashSum (.inr (.TLit : Typ 1)) sigC sigB =
    astHash (.TLit : Typ 1) sigC sigB := rfl

end hash

section recarrier

-- Opening nested UId binders preserves the outer receipt and substitutes the newest slot.
#guard
  let root : Root := ⟨Nat⟩
  let body : root.Binder .trm := .mk (λ outer =>
    .pure (.val (.fn .TLit (.mk (λ inner =>
      .apply (.pure (.ref outer (.lower .same))) (.pure (.ref inner .same)))))))
  match Root.Binder.apply body 7 with
  | .pure (.val (.fn _ nested)) =>
    match Root.Binder.apply nested 9 with
    | .apply (.pure (.ref outer underOuter)) (.pure (.ref inner underInner)) =>
      Nat.beq (Root.mapRef underOuter outer) 7 && Nat.beq (Root.mapRef underInner inner) 9
    | _ => false
  | _ => false

end recarrier

end Tests.STLC.HashSpec
