import «Lp2lc».Active.STLC.Hash

namespace Tests.STLC.HashSpec

open Lean (Json toJson)
open Lp2lc.Active.Util Lp2lc.Active.STLC

-- A constant increment lets distinct references inhabit the same AST index.
private abbrev P : Parameters := { C := Nat, B := String, inc := λ _ => 0 }

private def sigC (carrier : Nat) : Json := toJson carrier
private def sigB (repr : String) : Json := toJson repr
private def sigAny (_carrier : Nat) : Json := .null

private def refOne : AST.Trm (P := P) 0 := .ref (P := P) (c := 1) ⟨⟩
private def refTwo : AST.Trm (P := P) 0 := .ref (P := P) (c := 2) ⟨⟩
private def idVal : AST.Val (P := P) 1 := .fn .TLit (.mk (λ proxy => .ref proxy))

example : astToJson (.TLit : AST.Typ (P := P) 0) sigC sigB = "primitive" := rfl

example : astToJson (.TFn .TLit .TLit : AST.Typ (P := P) 0) sigC sigB =
    .arr #["fn", "primitive", "primitive"] := rfl

example : astToJson (.lit "x" : AST.Val (P := P) 0) sigC sigB =
    .arr #["lit", toJson ("x" : String)] := rfl

example : astToJson idVal sigC sigB =
    .arr #["lam", .arr #["ref", toJson (1 : Nat)], "primitive"] := rfl

example : astToJson (.val (.lit "x") : AST.Trm (P := P) 0) sigC sigB =
    .arr #["val", .arr #["lit", toJson ("x" : String)]] := rfl

example : astToJson (.apply refOne refTwo : AST.Trm (P := P) 0) sigC sigB =
    .arr #["apply", .arr #["ref", toJson (1 : Nat)],
      .arr #["ref", toJson (2 : Nat)]] := rfl

example : (astToJson refOne sigC sigB == astToJson refTwo sigC sigB) = false := by native_decide

example : astBEq refOne refTwo sigC sigB = false := by native_decide

example : astBEq refOne refTwo sigAny sigB = true := by native_decide

example : astHash refOne sigAny sigB = astHash refTwo sigAny sigB := rfl

example : hashSum (.inl idVal) sigC sigB = astHash idVal sigC sigB := rfl

example : hashSum (.inr (.TLit : AST.Typ (P := P) 1)) sigC sigB =
    astHash (.TLit : AST.Typ (P := P) 1) sigC sigB := rfl

end Tests.STLC.HashSpec
