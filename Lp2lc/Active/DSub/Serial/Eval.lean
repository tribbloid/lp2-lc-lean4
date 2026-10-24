import «Lp2lc».Active.DSub.Serial.Infer

namespace Lp2lc.Active.DSub.AST

open Lp2lc.Active.Util

/-- Evaluate with lexical captures, preserving rejection separately from runtime corruption.
Recursive resolution consumes fuel; primitive results are checked against their dependent annotations. -/
def eval {n} (self : Trm n) (bindings : ExeBindings := .empty) : RecOpt (Return ExeVal) := λ fuel =>
  match fuel, self with
  | 0, _ => .outOfFuel
  | fuel + 1, .val (.ref _ under) =>
    match bindings under.sourceIndex.down with
    | none => .yield none
    | some value =>
      match value.value with
      | .ref _ _ => eval value.value.asTrm value.captured fuel
      | _ => .yield (some (.some value))
  | _ + 1, .val value => .yield (some (.some ⟨n, value, bindings⟩))
  | fuel + 1, .apply fn arg =>
    match eval fn bindings fuel, eval arg bindings fuel with
    | .yield (some (.some ⟨context, .fn _ body, captured⟩)), .yield (some (.some value)) =>
      eval (body.apply .only) (captured.set (context + 1) value) fuel
    | .yield (some (.some ⟨context, .fnPrimitive output op, captured⟩)), .yield (some (.some argument)) =>
      match argument.value with
      | .lit repr =>
        let value : Val context := op repr
        -- An exact member declaration resolves the result annotation using this literal argument.
        match infer (.val (.typeDef (output.apply .only))) (captured.set (context + 1) argument) fuel,
            value.asTrm.infer captured fuel with
        | .yield (some ⟨index, .TMember _ expected, typeCaptures⟩), .yield (some actual) =>
          (actual.subtype ⟨index, expected, typeCaptures⟩ .empty fuel).flatMap (λ accepted =>
            if accepted then eval value.asTrm captured fuel else .yield (some .corrupted))
        | .outOfFuel, _ => .outOfFuel
        | _, .outOfFuel => .outOfFuel
        | _, _ => .yield (some .corrupted)
      | _ => .yield none
    | .yield (some .corrupted), .yield (some _)
    | .yield (some _), .yield (some .corrupted) => .yield (some .corrupted)
    | .yield _, .yield _ => .yield none
    | _, _ => .outOfFuel

namespace Monotone

/-- Completed evaluation results are preserved when fuel increases. -/
theorem termEval {n} (trm : Trm n) (bindings : ExeBindings) :
    (eval trm bindings).Monotone := by
  sorry

end Monotone

end Lp2lc.Active.DSub.AST
