import «Lp2lc».Active.DTLC.Serial.Infer

namespace Lp2lc.Active.DTLC.AST

open Lp2lc.Active.Util

variable {n : Nat}

namespace CertifiedByInfer

/-- A returned value certified at the caller's independently inferred type. -/
abbrev CertifiedVal (typ : Typ) :=
  {value : ExeVal // (value.value.asTrm.infer value.captured).isDecidable (· = typ)}

/-- Corruption is an allowed runtime exit; evaluation may also exhaust its fuel. -/
abbrev Result (typ : Typ) := Rec (Return (CertifiedVal typ))

private def evalInternal {n} (self : Trm n) (bindings : ExeBindings) : Rec (Return ExeVal) := λ fuel =>
  -- TODO: delete it, "eval_certified should build certified result in every step"
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield (.some ⟨n, value, bindings⟩)
    | .ref _ under =>
      match bindings under.sourceIndex.down with
      | some value => .yield (.some value)
      | none => .outOfFuel
    | .apply fn arg =>
      match evalInternal fn bindings fuel, evalInternal arg bindings fuel with
      | .yield (.some ⟨context, .fn _ body, captured⟩), .yield (.some argument) =>
        evalInternal (body.apply .only) (captured.set (context + 1) argument) fuel
      | .yield (.some ⟨context, .fnPrimitive output op, captured⟩),
          .yield (.some ⟨_, .lit repr, _⟩) =>
        let value : Val context := op repr
        match value.asTrm.infer captured fuel with
        | .yield (some actual) =>
          match actual.sameType (output.apply .only) fuel with
          | .yield true => .yield (.some ⟨context, value, captured⟩)
          | .yield false => .yield .corrupted
          | .outOfFuel => .outOfFuel
        | .yield none => .yield .corrupted
        | .outOfFuel => .outOfFuel
      | .yield .corrupted, .yield _
      | .yield _, .yield .corrupted => .yield .corrupted
      | _, _ => .outOfFuel

end CertifiedByInfer

open CertifiedByInfer

/-- Conjectured soundness: evaluation certifies returned values at the independently inferred type.
The evaluator is executable; only its type-preservation certificate is left unproved.
-/
def eval_certified (self : Trm n) (bindings : ExeBindings := .empty)
    {inferFuel : Nat} {typ : Typ}
    (_hInfer : self.infer bindings inferFuel = .yield (some typ)) : Result typ := λ fuel =>
  (evalInternal self bindings fuel).map (·.map (λ value => ⟨value, by sorry⟩))

end Lp2lc.Active.DTLC.AST
