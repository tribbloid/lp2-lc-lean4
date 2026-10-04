import «Lp2lc».Active.STLC.Hash

namespace Tests.STLC.HashSpec

open Lean (Json toJson)
open Lp2lc.Active.Util Lp2lc.Active.STLC

private def sigC (index : Nat) : Json := toJson index
private def sigB (repr : String) : Json := toJson repr
private def sigAny (_index : Nat) : Json := .null

private def capturedRef (useOuter : Bool) : Val 1 :=
  .fn .TLit (.mk (λ proxy =>
    if useOuter then .ref (lower := 1) .only (.lower (.lower .same))
    else .ref proxy .same))

private def idVal : Val 1 :=
  .fn .TLit (.mk (λ proxy => .ref proxy .same))

example : astToJson (.ref .only .same : Trm 0) sigC sigB =
    .arr #["ref", toJson (0 : Nat)] := rfl

example : astToJson (.ref .only .same : Trm 3) sigC sigB =
    .arr #["ref", toJson (3 : Nat)] := rfl

example : astToJson (.TLit : AST 0 .typ) sigC sigB = "primitive" := rfl

example : astToJson (.TFn .TLit .TLit : AST 0 .typ) sigC sigB =
    .arr #["fn", "primitive", "primitive"] := rfl

example : astToJson (.lit "x" : AST 0 .val) sigC sigB =
    .arr #["lit", toJson ("x" : String)] := rfl

example : astToJson idVal sigC sigB =
    .arr #["lam", .arr #["ref", toJson (3 : Nat)], "primitive"] := rfl

example : astToJson (.val (.lit "x") : AST 0 .trm) sigC sigB =
    .arr #["val", .arr #["lit", toJson ("x" : String)]] := rfl

example : astToJson (.apply (.val (capturedRef true)) (.val (capturedRef false)) : Trm 1) sigC sigB =
    .arr #["apply", .arr #["val", .arr #["lam", .arr #["ref", toJson (1 : Nat)], "primitive"]],
      .arr #["val", .arr #["lam", .arr #["ref", toJson (3 : Nat)], "primitive"]]] := rfl

example : (astToJson (capturedRef true) sigC sigB == astToJson (capturedRef false) sigC sigB) = false :=
  by native_decide

example : astBEq (capturedRef true) (capturedRef false) sigC sigB = false := by native_decide

example : astBEq (capturedRef true) (capturedRef false) sigAny sigB = true := by native_decide

example : astHash (capturedRef true) sigAny sigB = astHash (capturedRef false) sigAny sigB := rfl

example : hashSum (.inl idVal) sigC sigB = astHash idVal sigC sigB := rfl

example : hashSum (.inr (.TLit : Typ 1)) sigC sigB =
    astHash (.TLit : Typ 1) sigC sigB := rfl

end Tests.STLC.HashSpec
