import Mathlib.Tactic

namespace Lp2lc.Active.STLC.SI

structure Later (step : Prop) : Prop where
  force : step

inductive Ty : Type
| base : Ty
| arrow : (input : Ty) → (output : Ty) → Ty
deriving DecidableEq, Repr

abbrev Env := List Ty

inductive Variable : (env : Env) → (type : Ty) → Type where
| zero : Variable (type :: env) type
| successor : (index : Variable env type) → Variable (head_type :: env) type

inductive Term : (env : Env) → (type : Ty) → Type where
| term_variable : (index : Variable env type) → Term env type
| unit : Term env Ty.base
| lambda : (body : Term (input :: env) output) → Term env (Ty.arrow input output)
| apply : (function : Term env (Ty.arrow input output)) → (argument : Term env input) → Term env output

def Denotation : (type : Ty) → Type
| .base => PUnit
| .arrow input output => Denotation input → Denotation output

def Valuation : (env : Env) → Type
| [] => PUnit
| type :: env => Denotation type × Valuation env

def lookup : (index : Variable env type) → (valuation : Valuation env) → Denotation type
| .zero, (v, _) => v
| .successor index, (_, valuation) => lookup index valuation

def denote : (term : Term env type) → (valuation : Valuation env) → Denotation type
| .term_variable index, valuation => lookup index valuation
| .unit, _ => PUnit.unit
| .lambda body, valuation => fun value => denote body (value, valuation)
| .apply function argument, valuation => (denote function valuation) (denote argument valuation)

def Semantics : (type : Ty) → (steps : Nat) → Denotation type → Prop
| .base, _, _ => True
| .arrow input output, steps, function =>
    ∀ smaller_steps, smaller_steps ≤ steps →
      ∀ value, Semantics input smaller_steps value →
        Later (Semantics output smaller_steps (function value))

def EnvironmentSemantics : (env : Env) → (steps : Nat) → Valuation env → Prop
| [], _, _ => True
| type :: env, steps, (value, valuation) => Semantics type steps value ∧ EnvironmentSemantics env steps valuation

theorem Semantics.monotone {type : Ty} {smaller_steps steps : Nat} {value : Denotation type}
    (bound : smaller_steps ≤ steps) :
    Semantics type steps value → Semantics type smaller_steps value := by
  induction type generalizing smaller_steps steps with
  | base =>
      intro _
      trivial
  | arrow input output _ _ =>
      intro function_semantics test_steps test_bound test_value test_semantics
      exact function_semantics test_steps (le_trans test_bound bound) test_value test_semantics

theorem EnvironmentSemantics.monotone
    {env : Env} {smaller_steps steps : Nat} {valuation : Valuation env}
    (bound : smaller_steps ≤ steps) :
    EnvironmentSemantics env steps valuation → EnvironmentSemantics env smaller_steps valuation := by
  induction env generalizing smaller_steps steps with
  | nil =>
      intro _
      trivial
  | cons type env induction_hypothesis =>
      intro valuation_semantics
      rcases valuation_semantics with ⟨value_semantics, env_semantics⟩
      exact ⟨Semantics.monotone bound value_semantics, induction_hypothesis bound env_semantics⟩

theorem lookup_semantics {env : Env} {type : Ty} (index : Variable env type) :
    ∀ {steps : Nat} {valuation : Valuation env},
      EnvironmentSemantics env steps valuation → Semantics type steps (lookup index valuation) := by
  induction index with
  | zero =>
      intro _ _
      exact And.left
  | successor index induction_hypothesis =>
      intro _ _ valuation_semantics
      exact induction_hypothesis (And.right valuation_semantics)

theorem fundamental {env : Env} {type : Ty} (term : Term env type) :
    ∀ {steps : Nat} {valuation : Valuation env},
      EnvironmentSemantics env steps valuation → Semantics type steps (denote term valuation) := by
  induction term with
  | term_variable index =>
      intro _ _ valuation_semantics
      simpa [denote] using lookup_semantics index valuation_semantics
  | unit =>
      intro _ _ _
      trivial
  | lambda body induction_hypothesis =>
      intro steps valuation valuation_semantics smaller_steps smaller_bound value value_semantics
      have smaller_env_semantics := EnvironmentSemantics.monotone smaller_bound valuation_semantics
      exact ⟨induction_hypothesis (steps := smaller_steps) (valuation := (value, valuation))
        ⟨value_semantics, smaller_env_semantics⟩⟩
  | apply function argument function_induction argument_induction =>
      intro steps valuation valuation_semantics
      exact (function_induction valuation_semantics steps le_rfl
        (denote argument valuation) (argument_induction valuation_semantics)).force

abbrev closed (type : Ty) := Term [] type

theorem soundness {type : Ty} (term : closed type) :
    ∀ steps, Semantics type steps (denote term PUnit.unit) := by
  intro steps
  exact fundamental term trivial

end Lp2lc.Active.STLC.SI
