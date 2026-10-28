import «Lp2lc».Active.STLC_minimal.Serial.Infra
namespace Lp2lc.Active.STLC_minimal
open Lp2lc.Active.Util

namespace AST
variable {P : Parameters}

local instance typLE : LE (Pre.AST P .typ) := ⟨Eq⟩

@[instance_reducible]
local instance typDecidableLE : DecidableLE (Pre.AST P .typ)
  | .TLit, .TLit => isTrue rfl
  | .TLit, .TFn _ _
  | .TFn _ _, .TLit => isFalse (λ equality => nomatch equality)
  | .TFn a b, .TFn c d =>
    @decidable_of_iff' _ _ (Pre.AST.TFn.injEq a b c d).to_iff
      (@instDecidableAnd _ _ (typDecidableLE a c) (typDecidableLE b d))

def infer {n} (self : Trm n) (bindings : CompilerBindings := .empty) : RecOpt Typ := λ fuel =>
  match fuel, self with
  | 0, _ => .outOfFuel
  | _ + 1, .val (.lit _) => .yield (some .TLit)
  | fuel + 1, .val (.fn tIn body) =>
    (infer (body.apply .only)
      (bindings.set (n + 1) ⟨n, tIn, .empty⟩) fuel).map (Option.map (.TFn (resolveType tIn)))
  | fuel + 1, .ref _ under =>
    match bindings under.sourceIndex.down with
    | some (.inl ⟨_, typ, _⟩) => .yield (some typ.resolveType)
    | some (.inr ⟨_, value, captured⟩) => infer value.asTrm captured fuel
    | none => .yield none
  | fuel + 1, .apply fn arg =>
    match infer fn bindings fuel, infer arg bindings fuel with
    | .yield (some (.TFn tIn tOut)), .yield (some argTyp) =>
      .yield (if argTyp ≤ tIn then some tOut else none)
    | .yield _, .yield _ => .yield none
    | _, _ => .outOfFuel
  | _ + 1, .val (.fnPrimitive tOut _) => .yield (some (.TFn .TLit (resolveType tOut)))

def semType {n} (self : Trm n) (bindings : CompilerBindings) (fuel : Nat) (typ: Typ) :=
  self.infer bindings fuel = .yield (.some typ)

variable {n : Nat}

namespace Monotone

theorem termInfer (trm : Trm n)
    (bindings : CompilerBindings) :
    (infer trm bindings).Monotone := by
  intro less more result hFuel hInfer
  induction less generalizing n trm bindings more result with
  | zero => simp [infer] at hInfer
  | succ fuel ih =>
    cases more <;> try (exact False.elim (Nat.not_succ_le_zero _ hFuel))
    replace hFuel := Nat.le_of_succ_le_succ hFuel
    cases trm <;> try cases ‹Val n›
    all_goals
      simp only [infer.eq_2, infer.eq_3, infer.eq_4, infer.eq_5, infer.eq_6,
        Rec.Outcome.map] at hInfer ⊢
      repeat split at hInfer
      all_goals simp_all

end Monotone

end AST
end Lp2lc.Active.STLC_minimal
