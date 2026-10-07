import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util

/-- Finite source-index bindings, newest entry first. -/
structure Bindings (α : Type 1) where
  entries : List (Nat × α)

namespace Bindings

variable {α β : Type 1} (self : Bindings α)

def empty : Bindings α := ⟨[]⟩

instance : CoeFun (Bindings α) (λ _ => Nat → Option α) := ⟨λ self index => self.entries.lookup index⟩

def set (index : Nat) (value : α) : Bindings α := ⟨(index, value) :: self.entries⟩

def map (f : α → β) : Bindings β := ⟨self.entries.map (λ entry => (entry.1, f entry.2))⟩

@[simp] theorem getMap (f : α → β) (index : Nat) :
    self.map f index = (self index).map f := by
  rcases self with ⟨keys, values⟩
  induction keys <;> simp_all [map, get, Function.comp_def, apply_ite]

end Bindings

-- set_option genSizeOf false in
/-- A source value together with the bindings captured when it was evaluated. -/
structure ExeValue : Type 1 where
  n : Nat
  value : Val n
  captured : Bindings ExeValue

abbrev ExeBindings := Bindings ExeValue -- append-only

namespace AST

/-- Evaluate using the caller's bindings. Every recursive resolution consumes one unit of fuel. -/
def eval {n} (self : Trm n) (bindings : ExeBindings := .empty) : RecOpt ExeValue := λ fuel =>
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match self with
    | .val value => .yield (some (.mk n value bindings))
    | .ref _ under => .yield (bindings under.sourceIndex)
    | .apply fn arg =>
      match eval fn bindings fuel, eval arg bindings fuel with
      | .yield (some (.mk context (.fn _ body) captured)), .yield (some value) =>
        eval (body.apply .only)
          (captured.set (context + 1) value) fuel
      | .yield _, .yield _ => .yield none
      | _, _ => .outOfFuel

/-- Evaluation that succeeds with smaller fuel succeeds with the same value at larger fuel. -/
theorem termEvalMonotone {n} (trm) (bindings : ExeBindings) :
    (eval (n := n) trm bindings).Monotone := by
  intro less more result hFuel hEval
  induction less generalizing n trm bindings more result with
  | zero => simp [eval] at hEval
  | succ fuel ih =>
    cases more <;> try (exact False.elim (Nat.not_succ_le_zero _ hFuel))
    replace hFuel := Nat.le_of_succ_le_succ hFuel
    cases trm <;> simp only [eval.eq_2, eval.eq_3, eval.eq_4] at hEval ⊢
    all_goals
      repeat split at hEval
      all_goals simp_all

end AST

end Lp2lc.Active.STLC
