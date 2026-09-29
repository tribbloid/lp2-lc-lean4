import «Lp2lc».Active.STLC.Hash

namespace Tests.STLC.HashSpec

open Lean (Json toJson)
open Lp2lc.Active.Util Lp2lc.Active.STLC

private def sigC (index : Nat) : Json := toJson index
private def sigB (repr : String) : Json := toJson repr
private def sigAny (_index : Nat) : Json := .null

private def refOne : AST.Trm (AST.At 3) :=
  AST.ref (.inl (.inl (.inr .only)))

private def refTwo : AST.Trm (AST.At 3) :=
  AST.ref (.inl (.inr .only))

private def idVal : AST.Val (AST.At 1) := .fn .TLit (.mk (λ proxy => .ref proxy))

example : astToJson (AST.ref (.inl .only) : AST.Trm (AST.At 1)) sigC sigB =
    .arr #["ref", toJson (0 : Nat)] := rfl

example : astToJson (AST.ref (.inr .only) : AST.Trm (AST.At 1)) sigC sigB =
    .arr #["ref", toJson (1 : Nat)] := rfl

example : astToJson (.TLit : AST.Typ (AST.At 0)) sigC sigB = "primitive" := rfl

example : astToJson (.TFn .TLit .TLit : AST.Typ (AST.At 0)) sigC sigB =
    .arr #["fn", "primitive", "primitive"] := rfl

example : astToJson (.lit "x" : AST.Val (AST.At 0)) sigC sigB =
    .arr #["lit", toJson ("x" : String)] := rfl

example : astToJson idVal sigC sigB =
    .arr #["lam", .arr #["ref", toJson (2 : Nat)], "primitive"] := rfl

example : astToJson (.val (.lit "x") : AST.Trm (AST.At 0)) sigC sigB =
    .arr #["val", .arr #["lit", toJson ("x" : String)]] := rfl

example : astToJson (.apply refOne refTwo : AST.Trm (AST.At 3)) sigC sigB =
    .arr #["apply", .arr #["ref", toJson (1 : Nat)],
      .arr #["ref", toJson (2 : Nat)]] := rfl

example : (astToJson refOne sigC sigB == astToJson refTwo sigC sigB) = false := by native_decide

example : astBEq refOne refTwo sigC sigB = false := by native_decide

example : astBEq refOne refTwo sigAny sigB = true := by native_decide

example : astHash refOne sigAny sigB = astHash refTwo sigAny sigB := rfl

example : hashSum (.inl idVal) sigC sigB = astHash idVal sigC sigB := rfl

example : hashSum (.inr (.TLit : AST.Typ (AST.At 1))) sigC sigB =
    astHash (.TLit : AST.Typ (AST.At 1)) sigC sigB := rfl

end Tests.STLC.HashSpec
