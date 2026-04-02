import Mathlib.Tactic
import «Lp2lc».Active.Shared

namespace Lp2lc.Active.STLC.SI

structure Later (step : Prop) : Prop where
  force : step

inductive Ty : Type
| base : Ty
| arrow : (input : Ty) → (output : Ty) → Ty
deriving DecidableEq, Repr

abbrev Env := List (Var × Ty)

namespace Env

def get (name : Var) : Env → Option Ty
| [] => none
| (bound_name, type) :: env =>
    if name = bound_name then
      some type
    else
      get name env

end Env

namespace exp

  inductive Term : Ty -> Type where
  | term_variable : Var -> Term type
  | unit : Term Ty.base
  | lambda : Var -> Term output -> Term (Ty.arrow input output)
  | apply : Term (Ty.arrow input output) -> Term input -> Term output

  def Scoped (Γ : Env) {type : Ty}: Term type → Prop
  | .term_variable x => Γ.get x = some type
  | .unit => True
  | @Term.lambda _ input x body => Scoped ((x, input) :: Γ) body
  | @Term.apply _ _ f a => Scoped Γ f ∧ Scoped Γ a

end exp

inductive Term : (env : Env) → (type : Ty) → Type where
| term_variable : (name : Var) → (binding : env.get name = some type) → Term env type
| unit : Term env Ty.base
| lambda : (name : Var) → (body : Term ((name, input) :: env) output) → Term env (Ty.arrow input output)
| apply : (function : Term env (Ty.arrow input output)) → (argument : Term env input) → Term env output

def Denotation : (type : Ty) → Type
| .base => PUnit
| .arrow input output => Denotation input → Denotation output

def Valuation (env : Env): Type := ∀ (name : Var) (type : Ty), env.get name = some type → Denotation type

def extend (valuation : Valuation env) (name : Var) (value : Denotation input) :
    Valuation ((name, input) :: env)
| tested_name, type, binding =>
    if same_name : tested_name = name then
      by
        subst same_name
        simp [Env.get] at binding
        cases binding
        exact value
    else
      valuation tested_name type (by simpa [Env.get, same_name] using binding)

def denote : (term : Term env type) → (valuation : Valuation env) → Denotation type
| .term_variable name binding, valuation => valuation name type binding
| .unit, _ => PUnit.unit
| .lambda name body, valuation => fun value => denote body (extend valuation name value)
| .apply function argument, valuation => (denote function valuation) (denote argument valuation)

def Semantics : (type : Ty) → (steps : Nat) → Denotation type → Prop
| .base, _, _ => True
| .arrow input output, steps, function =>
    ∀ smaller_steps, smaller_steps ≤ steps →
      ∀ value, Semantics input smaller_steps value →
        Later (Semantics output smaller_steps (function value))

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

def EnvironmentSemantics (env : Env) (steps : Nat) (valuation : Valuation env) : Prop :=
  ∀ (name : Var) (type : Ty) (binding : env.get name = some type),
    Semantics type steps (valuation name type binding)

theorem EnvironmentSemantics.monotone
    {env : Env} {smaller_steps steps : Nat} {valuation : Valuation env}
    (bound : smaller_steps ≤ steps) :
    EnvironmentSemantics env steps valuation → EnvironmentSemantics env smaller_steps valuation := by
  intro valuation_semantics name type binding
  exact Semantics.monotone bound (valuation_semantics name type binding)

theorem extend_semantics {env : Env} {input : Ty} {steps : Nat} {valuation : Valuation env}
    (valuation_semantics : EnvironmentSemantics env steps valuation)
    {name : Var} {value : Denotation input} (value_semantics : Semantics input steps value) :
    EnvironmentSemantics ((name, input) :: env) steps (extend valuation name value) := by
  intro tested_name type binding
  by_cases same_name : tested_name = name
  · subst same_name
    simp [extend, Env.get] at binding ⊢
    cases binding
    simpa [extend, Env.get] using value_semantics
  · have tail_binding : env.get tested_name = some type := by
      simpa [Env.get, same_name] using binding
    simpa [extend, same_name] using valuation_semantics tested_name type tail_binding

theorem fundamental {env : Env} {type : Ty} (term : Term env type) :
    ∀ {steps : Nat} {valuation : Valuation env},
      EnvironmentSemantics env steps valuation → Semantics type steps (denote term valuation) := by
  induction term with
  | term_variable name binding =>
      intro _ _ valuation_semantics
      simpa [denote] using valuation_semantics name _ binding
  | unit =>
      intro _ _ _
      trivial
  | lambda name body induction_hypothesis =>
      intro steps valuation valuation_semantics smaller_steps smaller_bound value value_semantics
      exact ⟨induction_hypothesis (steps := smaller_steps) (valuation := extend valuation name value)
        (extend_semantics (EnvironmentSemantics.monotone smaller_bound valuation_semantics) value_semantics)⟩
  | apply function argument function_induction argument_induction =>
      intro steps valuation valuation_semantics
      exact (function_induction valuation_semantics steps le_rfl
        (denote argument valuation) (argument_induction valuation_semantics)).force

abbrev closed (type : Ty) := Term [] type

def empty_valuation : Valuation [] := by
  intro name type binding
  simp [Env.get] at binding

namespace exp

def denote {env : Env} {type : Ty} (term : exp.Term type) :
    exp.Scoped env term → Valuation env → Denotation type :=
  match term with
  | .term_variable name => fun hscoped => fun valuation => valuation name _ hscoped
  | .unit => fun _ => fun _ => PUnit.unit
  | @exp.Term.lambda output input name body => fun hscoped => fun valuation => fun (value : Denotation input) =>
      let body_scoped : exp.Scoped ((name, input) :: env) body := by
        simpa [exp.Scoped] using hscoped
      denote body body_scoped (extend valuation name value)
  | @exp.Term.apply input output function argument => fun hscoped => fun valuation =>
      (denote function hscoped.left valuation) (denote argument hscoped.right valuation)

theorem fundamental {env : Env} {type : Ty} (term : exp.Term type) :
    ∀ {steps : Nat} {valuation : Valuation env} (hscoped : exp.Scoped env term),
      EnvironmentSemantics env steps valuation →
      Semantics type steps (exp.denote term hscoped valuation) := by
  induction term generalizing env with
  | term_variable name =>
      intro _ valuation hscoped valuation_semantics
      simpa [exp.denote] using valuation_semantics name _ hscoped
  | unit =>
      intro _ _ _ _
      trivial
  | @lambda output input name body induction_hypothesis =>
      intro steps valuation hscoped valuation_semantics smaller_steps smaller_bound value value_semantics
      have body_scoped : exp.Scoped ((name, input) :: env) body := by
        simpa [exp.Scoped] using hscoped
      exact ⟨induction_hypothesis (env := (name, input) :: env) (steps := smaller_steps)
        (valuation := extend valuation name value) body_scoped
        (extend_semantics (EnvironmentSemantics.monotone smaller_bound valuation_semantics) value_semantics)⟩
  | @apply input output function argument function_induction argument_induction =>
      intro steps valuation hscoped valuation_semantics
      exact (function_induction (valuation := valuation) hscoped.left valuation_semantics steps le_rfl
        (exp.denote argument hscoped.right valuation)
        (argument_induction (valuation := valuation) hscoped.right valuation_semantics)).force

abbrev closed (type : Ty) := { term : exp.Term type // exp.Scoped [] term }

theorem soundness {type : Ty} (term : closed type) :
    ∀ steps, Semantics type steps (exp.denote term.1 term.2 empty_valuation) := by
  intro steps
  exact exp.fundamental term.1 (valuation := empty_valuation) term.2 (by
    intro name inner_type binding
    simp [Env.get] at binding)

end exp

theorem soundness {type : Ty} (term : closed type) :
    ∀ steps, Semantics type steps (denote term empty_valuation) := by
  intro steps
  exact fundamental term (valuation := empty_valuation) (by
    intro name inner_type binding
    simp [Env.get] at binding)

end Lp2lc.Active.STLC.SI
