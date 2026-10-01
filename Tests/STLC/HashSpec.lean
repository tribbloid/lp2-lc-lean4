import «Lp2lc».Active.STLC.Hash

namespace Tests.STLC.HashSpec

open Lean (Json toJson)
open Lp2lc.Active.Util Lp2lc.Active.STLC

private def sigC (index : Nat) : Json := toJson index
private def sigB (repr : String) : Json := toJson repr
private def sigAny (_index : Nat) : Json := .null

private def refOne : Pre.AST CtxEmbedding.DeBruijn.toParameters.Next.Next.Next .trm :=
  Pre.AST.ref (.inl (.inl (.inr .only)))

private def refTwo : Pre.AST CtxEmbedding.DeBruijn.toParameters.Next.Next.Next .trm :=
  Pre.AST.ref (.inl (.inr .only))

private def idVal : Pre.AST CtxEmbedding.DeBruijn.toParameters.Next .val := .fn .TLit (.mk (λ proxy => .ref proxy))

example : astToJson (Pre.AST.ref (.inl .only) : Pre.AST CtxEmbedding.DeBruijn.toParameters.Next .trm) sigC sigB =
    .arr #["ref", toJson (0 : Nat)] := rfl

example : astToJson (Pre.AST.ref (.inr .only) : Pre.AST CtxEmbedding.DeBruijn.toParameters.Next .trm) sigC sigB =
    .arr #["ref", toJson (1 : Nat)] := rfl

example : astToJson (.TLit : AST 0 .typ) sigC sigB = "primitive" := rfl

example : astToJson (.TFn .TLit .TLit : AST 0 .typ) sigC sigB =
    .arr #["fn", "primitive", "primitive"] := rfl

example : astToJson (.lit "x" : AST 0 .val) sigC sigB =
    .arr #["lit", toJson ("x" : String)] := rfl

example : astToJson idVal sigC sigB =
    .arr #["lam", .arr #["ref", toJson (2 : Nat)], "primitive"] := rfl

example : astToJson (.val (.lit "x") : AST 0 .trm) sigC sigB =
    .arr #["val", .arr #["lit", toJson ("x" : String)]] := rfl

example : astToJson (.apply refOne refTwo : Pre.AST CtxEmbedding.DeBruijn.toParameters.Next.Next.Next .trm) sigC sigB =
    .arr #["apply", .arr #["ref", toJson (1 : Nat)],
      .arr #["ref", toJson (2 : Nat)]] := rfl

example : (astToJson refOne sigC sigB == astToJson refTwo sigC sigB) = false := by native_decide

example : astBEq refOne refTwo sigC sigB = false := by native_decide

example : astBEq refOne refTwo sigAny sigB = true := by native_decide

example : astHash refOne sigAny sigB = astHash refTwo sigAny sigB := rfl

example : hashSum (.inl idVal) sigC sigB = astHash idVal sigC sigB := rfl

example : hashSum (.inr (.TLit : Pre.AST CtxEmbedding.DeBruijn.toParameters.Next .typ)) sigC sigB =
    astHash (.TLit : Pre.AST CtxEmbedding.DeBruijn.toParameters.Next .typ) sigC sigB := rfl

end Tests.STLC.HashSpec
