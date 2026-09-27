import «Lp2lc».Active.STLC.Hash

namespace Tests.STLC.HashSpec

open Lean (Json toJson)
open Lp2lc.Active.Util Lp2lc.Active.STLC

private def sigC (carrier : Nat) : Json := toJson carrier
private def sigB (repr : String) : Json := toJson repr
private def sigAny (_carrier : Nat) : Json := .null

private def refOne : AST.Trm 3 :=
  Pre.AST.ref (P := DeBruijn) (c := 1) (target := 3) ⟨⟩

private def refTwo : AST.Trm 3 :=
  Pre.AST.ref (P := DeBruijn) (c := 2) (target := 3) ⟨⟩

private def idVal : AST.Val 1 := .fn .TLit (.mk (λ proxy => Pre.AST.ref (P := DeBruijn) proxy))

example : astToJson (.TLit : AST.Typ 0) sigC sigB = "primitive" := rfl

example : astToJson (.TFn .TLit .TLit : AST.Typ 0) sigC sigB =
    .arr #["fn", "primitive", "primitive"] := rfl

example : astToJson (.lit "x" : AST.Val 0) sigC sigB =
    .arr #["lit", toJson ("x" : String)] := rfl

example : astToJson idVal sigC sigB =
    .arr #["lam", .arr #["ref", toJson (1 : Nat)], "primitive"] := rfl

example : astToJson (.val (.lit "x") : AST.Trm 0) sigC sigB =
    .arr #["val", .arr #["lit", toJson ("x" : String)]] := rfl

example : astToJson (.apply refOne refTwo : AST.Trm 3) sigC sigB =
    .arr #["apply", .arr #["ref", toJson (1 : Nat)],
      .arr #["ref", toJson (2 : Nat)]] := rfl

example : (astToJson refOne sigC sigB == astToJson refTwo sigC sigB) = false := by native_decide

example : astBEq refOne refTwo sigC sigB = false := by native_decide

example : astBEq refOne refTwo sigAny sigB = true := by native_decide

example : astHash refOne sigAny sigB = astHash refTwo sigAny sigB := rfl

example : hashSum (.inl idVal) sigC sigB = astHash idVal sigC sigB := rfl

example : hashSum (.inr (.TLit : AST.Typ 1)) sigC sigB =
    astHash (.TLit : AST.Typ 1) sigC sigB := rfl

end Tests.STLC.HashSpec
