import «Lp2lc».Active.STLC.STLCDef

namespace Lp2lc.Active.STLC
open Lp2lc.Active.Util

/-- Total values in finite slots; keys preserve sparse source indices. -/
structure Bindings (α : Type 1) where
  keys : List Nat
  values (slot : Fin keys.length) : α

namespace Bindings

variable {α β : Type 1} (self : Bindings α)

def empty : Bindings α := ⟨[], Fin.elim0⟩

def get (index : Nat) (keys : List Nat) (values : Fin keys.length → α) : Option α :=
  match keys, values with
  | [], _ => none
  | key :: keys, values =>
    if index = key then some (values 0) else get index keys (λ slot => values slot.succ)

instance : CoeFun (Bindings α) (λ _ => Nat → Option α) := ⟨λ self index => get index self.keys self.values⟩

def set (index : Nat) (value : α) : Bindings α :=
  ⟨index :: self.keys, Fin.cases value self.values⟩

def map (f : α → β) : Bindings β := ⟨self.keys, f ∘ self.values⟩

end Bindings

set_option genSizeOf false in
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
    cases more with
    | zero => cases hFuel
    | succ more =>
      have hFuelTail := Nat.le_of_succ_le_succ hFuel
      cases trm <;> simp only [eval.eq_2, eval.eq_3, eval.eq_4] at hEval ⊢
      all_goals
        repeat split at hEval
        all_goals simp_all

end AST

end Lp2lc.Active.STLC
