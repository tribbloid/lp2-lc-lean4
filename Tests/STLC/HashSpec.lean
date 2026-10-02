import «Lp2lc».Active.STLC.Hash

namespace Tests.STLC.HashSpec

open Lean (Json toJson)
open Lp2lc.Active.Util Lp2lc.Active.STLC

local notation "𝒫" => CtxEmbedding.DeBruijn.toParameters

private def sigC (index : Nat) : Json := toJson index
private def sigB (repr : String) : Json := toJson repr
private def sigAny (_index : Nat) : Json := .null

private def refOne : Pre.AST (𝒫).Next.Next.Next .trm :=
  .ref (lower := (𝒫).Next) (.inr .only) (.lower (.lower .same))

private def refTwo : Pre.AST (𝒫).Next.Next.Next .trm :=
  .ref (lower := (𝒫).Next.Next) (.inr .only) (.lower .same)

private def idVal : Pre.AST (𝒫).Next .val :=
  .fn .TLit (.mk (λ proxy => .ref proxy .same))

example : astToJson (.ref (lower := 𝒫) .only (.lower .same) :
    Pre.AST (𝒫).Next .trm) sigC sigB 8 =
    .yield (.arr #["ref", toJson (0 : Nat)]) := rfl

example : astToJson (.ref (lower := (𝒫).Next) (.inr .only) .same :
    Pre.AST (𝒫).Next .trm) sigC sigB 8 =
    .yield (.arr #["ref", toJson (1 : Nat)]) := rfl

example : astToJson (.TLit : AST 0 .typ) sigC sigB 8 = .yield "primitive" := rfl

example : astToJson (.TFn .TLit .TLit : AST 0 .typ) sigC sigB 8 =
    .yield (.arr #["fn", "primitive", "primitive"]) := rfl

example : astToJson (.lit "x" : AST 0 .val) sigC sigB 8 =
    .yield (.arr #["lit", toJson ("x" : String)]) := rfl

example : astToJson idVal sigC sigB 8 =
    .yield (.arr #["lam", .arr #["ref", toJson (3 : Nat)], "primitive"]) := rfl

example : astToJson (.val (.lit "x") : AST 0 .trm) sigC sigB 8 =
    .yield (.arr #["val", .arr #["lit", toJson ("x" : String)]]) := rfl

example : astToJson (.apply refOne refTwo : Pre.AST (𝒫).Next.Next.Next .trm) sigC sigB 8 =
    .yield (.arr #["apply", .arr #["ref", toJson (1 : Nat)],
      .arr #["ref", toJson (2 : Nat)]]) := rfl

example : (astToJson refOne sigC sigB 8).map
    (λ json => json == .arr #["ref", toJson (2 : Nat)]) = .yield false := by
  apply congrArg Rec.Outcome.yield
  native_decide

example : astBEq refOne refTwo sigC sigB 8 = .yield false := by
  apply congrArg Rec.Outcome.yield
  native_decide

example : astBEq refOne refTwo sigAny sigB 8 = .yield true := by
  apply congrArg Rec.Outcome.yield
  native_decide

example : astHash refOne sigAny sigB 8 = astHash refTwo sigAny sigB 8 := rfl

example : hashSum (.inl idVal) sigC sigB 8 = astHash idVal sigC sigB 8 := rfl

example : hashSum (.inr (.TLit : Pre.AST (𝒫).Next .typ)) sigC sigB 8 =
    astHash (.TLit : Pre.AST (𝒫).Next .typ) sigC sigB 8 := rfl

example : astToJson (.TLit : AST 0 .typ) sigC sigB 0 = .outOfFuel := rfl

example : astToJson (.TFn .TLit .TLit : AST 0 .typ) sigC sigB 1 = .outOfFuel := rfl

example : astToJson idVal sigC sigB 1 = .outOfFuel := rfl

example : astToJson (.val (.lit "x") : AST 0 .trm) sigC sigB 1 = .outOfFuel := rfl

example : astBEq refOne refTwo sigC sigB 0 = .outOfFuel := rfl

example : astBEq refOne (.apply refOne refTwo) sigAny sigB 1 = .outOfFuel := rfl

example : astHash idVal sigC sigB 1 = .outOfFuel := rfl

example : hashSum (.inl idVal) sigC sigB 1 = .outOfFuel := rfl

end Tests.STLC.HashSpec
