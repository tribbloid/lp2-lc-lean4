import «Lp2lc».Active.STLC.Hash

namespace Tests.STLC.HashSpec

open Lean (Json toJson)
open Lp2lc.Active.Util Lp2lc.Active.STLC

local notation "𝒫" => CtxEmbedding.DeBruijn.toParameters

private def sigC (index : Nat) : Json := toJson index
private def sigB (repr : String) : Json := toJson repr
private def sigAny (_index : Nat) : Json := .null

private def refOne : Syntax (𝒫).Next.Next.Next .trm :=
  .ref (lower := (𝒫).Next) (.inr .only) (.lower (.lower .same))

private def refTwo : Syntax (𝒫).Next.Next.Next .trm :=
  .ref (lower := (𝒫).Next.Next) (.inr .only) (.lower .same)

private def idVal : Syntax (𝒫).Next .val :=
  .fn .TLit (.mk (λ proxy => .ref proxy .same))

example : astToJson (.ref (lower := 𝒫) .only (.lower .same) :
    Syntax (𝒫).Next .trm) sigC sigB =
    .arr #["ref", toJson (0 : Nat)] := rfl

example : astToJson (.ref (lower := (𝒫).Next) (.inr .only) .same :
    Syntax (𝒫).Next .trm) sigC sigB =
    .arr #["ref", toJson (1 : Nat)] := rfl

example : astToJson (.TLit : AST 0 .typ) sigC sigB = "primitive" := rfl

example : astToJson (.TFn .TLit .TLit : AST 0 .typ) sigC sigB =
    .arr #["fn", "primitive", "primitive"] := rfl

example : astToJson (.lit "x" : AST 0 .val) sigC sigB =
    .arr #["lit", toJson ("x" : String)] := rfl

example : astToJson idVal sigC sigB =
    .arr #["lam", .arr #["ref", toJson (3 : Nat)], "primitive"] := rfl

example : astToJson (.val (.lit "x") : AST 0 .trm) sigC sigB =
    .arr #["val", .arr #["lit", toJson ("x" : String)]] := rfl

example : astToJson (.apply refOne refTwo : Syntax (𝒫).Next.Next.Next .trm) sigC sigB =
    .arr #["apply", .arr #["ref", toJson (1 : Nat)],
      .arr #["ref", toJson (2 : Nat)]] := rfl

example : (astToJson refOne sigC sigB == astToJson refTwo sigC sigB) = false := by native_decide

example : astBEq refOne refTwo sigC sigB = false := by native_decide

example : astBEq refOne refTwo sigAny sigB = true := by native_decide

example : astHash refOne sigAny sigB = astHash refTwo sigAny sigB := rfl

example : hashSum (.inl idVal) sigC sigB = astHash idVal sigC sigB := rfl

example : hashSum (.inr (.TLit : Syntax (𝒫).Next .typ)) sigC sigB =
    astHash (.TLit : Syntax (𝒫).Next .typ) sigC sigB := rfl

end Tests.STLC.HashSpec
