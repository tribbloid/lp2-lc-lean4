import «Lp2lc».Next.STLC.STLCDef

namespace Lp2lc.Next.STLC

open Lp2lc.Active.Util

namespace AST

/-- Evaluates terms whose references carry receipts from the runtime context. -/
def eval {F : Free} [env : ExeEnv F]
    (self : Trm env.CVar) : RecOpt (Val env.CVar)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield (some value)
    | .apply fnTerm arg =>
      let anf := (eval fnTerm fuel, eval arg fuel)
      match anf with
      | (.yield (some (.lam body _tIn)), .yield (some input)) =>
        let receipt := env.trm2valCtx.inv ⟨arg, input⟩
        eval (body receipt) fuel
      | (.outOfFuel, _) => .outOfFuel
      | (_, .outOfFuel) => .outOfFuel
      | _ => .yield none
    | .ref receipt =>
      .yield (some (env.trm2valCtx.get receipt).val)

/-- Infers `CTyp` types for terms whose references carry runtime `CVar` receipts. -/
def infer {F : Free} [env : BuildEnv F]
    (self : Trm env.CVar) : RecOpt (Typ env.CTyp)
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val (.lit _) => .yield (some .primitive)
    | .val (.lam body tIn) =>
      let typingTerm : Trm env.CTyp := by
        sorry
      let receipt := env.trm2typCtx.inv
        ⟨typingTerm, Typ.recarrier tIn⟩
      let index : env.CVar.Carrier := ⟨receipt.fst, by sorry⟩
      (infer (body index) fuel).map
        (λ out => out.map (λ tOut => .fn (Typ.recarrier tIn) tOut))
    | .apply fnTerm arg =>
      match infer fnTerm fuel, infer arg fuel with
      | .yield (some (.fn tIn tOut)), .yield (some argTyp) =>
        if argTyp ≤ tIn then .yield (some tOut) else .yield none
      | .outOfFuel, _ => .outOfFuel
      | _, .outOfFuel => .outOfFuel
      | _, _ => .yield none
    | .ref receipt =>
      let typingReceipt : env.CTyp.Carrier := ⟨receipt.fst, by sorry⟩
      .yield (some (env.trm2typCtx.get typingReceipt).typ)

end AST

end Lp2lc.Next.STLC
