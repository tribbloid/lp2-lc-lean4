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

private def hasType (value : ExeVal) (expected : Typ n) : Rec Bool := λ fuel =>
  (value.value.asTrm.infer value.captured fuel).flatMap (λ actual =>
    match actual with
    | some actual => actual.sameType expected fuel
    | none => .yield false)

private def evalInternal {n} (self : Trm n) (bindings : ExeBindings) : Rec (Return ExeVal) := λ fuel =>
  -- TODO: this may be useless and needs to be removed, "eval_certified should build certified result in every step".
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
      | .yield (.some ⟨context, .fn input body, captured⟩), .yield (.some argument) =>
        (hasType argument input fuel).flatMap (λ accepted =>
          if accepted then evalInternal (body.apply .only) (captured.set (context + 1) argument) fuel
          else .yield .corrupted)
      | .yield (.some ⟨context, .fnPrimitive output op, captured⟩),
          .yield (.some ⟨_, .lit repr, _⟩) =>
        let value : ExeVal := ⟨context, op repr, captured⟩
        (hasType value (output.apply .only) fuel).map (λ accepted =>
          if accepted then .some value else .corrupted)
      | .yield .corrupted, .yield _
      | .yield _, .yield .corrupted => .yield .corrupted
      | _, _ => .outOfFuel

end CertifiedByInfer

/-- Conjectured soundness: evaluation certifies returned values at the independently inferred type.
The evaluator is executable; only its type-preservation certificate is left unproved.
-/
def eval_certified (self : Trm n) (bindings : ExeBindings := .empty)
    {inferFuel : Nat} {typ : Typ}
    (_hInfer : self.infer bindings inferFuel = .yield (some typ)) : CertifiedByInfer.Result typ := λ fuel =>
  (CertifiedByInfer.evalInternal self bindings fuel).map (·.map (λ value => ⟨value, by sorry⟩))

end Lp2lc.Active.DTLC.AST
