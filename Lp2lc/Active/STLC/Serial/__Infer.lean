import «Lp2lc».Active.STLC.Serial.Infra
namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util

namespace AST
variable {P : Parameters}

/-- Current STLC subtyping coincides with structural type equality. -/
local instance typLE : LE (Pre.AST P .typ) := ⟨Eq⟩

/-- Decides structural subtyping by source type equality for every carrier. -/
@[instance_reducible]
local instance typDecidableLE : DecidableLE (Pre.AST P .typ)
  | .TLit, .TLit => isTrue rfl
  | .TLit, .TFn _ _
  | .TFn _ _, .TLit => isFalse (λ equality => nomatch equality)
  | .TFn a b, .TFn c d =>
    @decidable_of_iff' _ _ (Pre.AST.TFn.injEq a b c d).to_iff
      (@instDecidableAnd _ _ (typDecidableLE a c) (typDecidableLE b d))

/-- Infer using runtime values or hypothetical types, resolving runtime values in their captured environments. -/
def inferInternal {n} (self : Trm n) (bindings : CompilerBindings) : RecOpt Typ := λ fuel =>
  match fuel, self with
  | 0, _ => .outOfFuel
  | _ + 1, .val (.lit _) => .yield (some .TLit)
  | fuel + 1, .val (.fn tIn body) =>
    (inferInternal (body.apply .only)
      (bindings.set (n + 1) (.inl ⟨n, tIn, .empty⟩)) fuel).map (Option.map (.TFn (resolveType tIn)))
  | fuel + 1, .ref _ under =>
    match bindings under.sourceIndex.down with
    | some (.inl ⟨_, typ, _⟩) => .yield (some typ.resolveType)
    | some (.inr ⟨_, value, captured⟩) => inferInternal value.asTrm (captured.map .inr) fuel
    | none => .yield none
  | fuel + 1, .apply fn arg =>
    match inferInternal fn bindings fuel, inferInternal arg bindings fuel with
    | .yield (some (.TFn tIn tOut)), .yield (some argTyp) =>
      .yield (if argTyp ≤ tIn then some tOut else none)
    | .yield _, .yield _ => .yield none
    | _, _ => .outOfFuel

/-- Infer using runtime values only, resolving each captured value to its type. -/ -- TODO: remove this? too trivial
def infer {n} (self : Trm n) (exeBindings : ExeBindings := .empty) : RecOpt Typ :=
  self.inferInternal (exeBindings.map .inr)

def semType {n} (self : Trm n) (bindings : CompilerBindings) (fuel : Nat) (typ: Typ) :=
  self.inferInternal bindings fuel = .yield (.some typ)

variable {n : Nat}

namespace Monotone

/-- Every completed inference result, including rejection, is preserved when fuel increases. -/
theorem termInfer (trm : Trm n)
    (bindings : CompilerBindings) :
    (inferInternal trm bindings).Monotone := by
  intro less more result hFuel hInfer
  induction less generalizing n trm bindings more result with
  | zero => simp [inferInternal] at hInfer
  | succ fuel ih =>
    cases more <;> try (exact False.elim (Nat.not_succ_le_zero _ hFuel))
    replace hFuel := Nat.le_of_succ_le_succ hFuel
    cases trm <;> try cases ‹Val n›
    all_goals
      simp only [inferInternal.eq_2, inferInternal.eq_3, inferInternal.eq_4, inferInternal.eq_5,
        Rec.Outcome.map] at hInfer ⊢
      repeat split at hInfer
      all_goals simp_all

/-- Runtime inference preserves every completed result when fuel increases. -/
theorem termInferRuntime (trm : Trm n) (bindings : ExeBindings := .empty) :
    (trm.infer bindings).Monotone := termInfer trm (bindings.map .inr)

end Monotone

end AST
end Lp2lc.Active.STLC
