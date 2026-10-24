import «Lp2lc».Active.DSub.Serial.Eval

namespace Lp2lc.Active.DSub.AST

open Lp2lc.Active.Util

namespace CertifiedByInfer

abbrev ConditionalVal (condition : CompilerTyp → Prop) :=
  {value : ExeVal // (value.value.asTrm.infer value.captured).isDecidable condition}

/-- A returned value whose independently inferred type passes the existing subtype check. -/
abbrev CertifiedVal (typ : CompilerTyp) :=
  ConditionalVal (λ actual => ∃ fuel, actual.subtype typ .empty fuel = .yield true)

/-- Fuel-bounded certified evaluation may still exhaust its fuel. -/
abbrev Result (typ : CompilerTyp) := Rec (CertifiedVal typ)

/-- Reuse ordinary evaluation and certify only independently checked returned values.
Rejection, corruption, and unsuccessful checks report `outOfFuel`.
A terminating accepted term may still lack a certificate at every fuel budget. -/
private def evalInternal {n} (self : Trm n) (bindings : ExeBindings) (typ : CompilerTyp) : Result typ := λ fuel =>
  match self.eval bindings fuel with
  | .yield (some (.some value)) =>
    match _hInfer : value.value.asTrm.infer value.captured fuel with
    | .yield (some actual) =>
      match _hSubtype : actual.subtype typ .empty fuel with
      | .yield true => .yield ⟨value, by sorry⟩
      | _ => .outOfFuel
    | _ => .outOfFuel
  | _ => .outOfFuel

end CertifiedByInfer

open CertifiedByInfer

/-- Evaluate an independently inferred term, checking its returned value at the inferred type. -/
def eval_certified {n} (self : Trm n) (bindings : ExeBindings := .empty)
    {inferFuel : Nat} {typ : CompilerTyp}
    (_hInfer : self.infer bindings inferFuel = .yield (some typ)) : Result typ :=
  evalInternal self bindings typ

end Lp2lc.Active.DSub.AST
