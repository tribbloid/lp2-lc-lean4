import Mathlib.Tactic
import «Lp2lc».Active.Shared

/-!
This file defines simply typed lambda calculus and relevant compiler components, with the following conventions:

- higher-order syntax representation: the data structure representing term variables is unknown and
  irrelevant, all proof must be valid regardless of the concrete data structure.
  - this means that Variable name, de Bruijn serial are not a thing
  - Environment/Context should be indexed by the unknown term parameter
- extrinsic/Curry-style type representations: types of terms are predicates instead of built-in index.
- interpretation is a step-indexed logical relation. The step index is the fuel used to
  reason about functions recursively: a function is safe for `steps` when, for
  any `smaller_steps < steps`, it sends semantically safe inputs to outputs that
  stay safe one guarded step later.

All docstrings use short (under 5 lines) of Scala code as demonstrations.

variable names always follow the following convention:

- Lean variable for type, proposition and sort of any universe should use PascalCase (e.g. `Env`)
  - inductive cases should use camelCase (because they are constructors)
- Lean variable for terms, functions & data should use camelCase (e.g. `Env.bind`)
  - variable for DOT types, pre-types (which are Lean data) should start with `t` (e.g. tIn, tOut)
- use full name, not acronym or abbreviation
-/

namespace Lp2lc.Active.STLC

structure Later (step : Prop) : Prop where
  force : step

def Instructions := String

section

variable {TermVar : Type}

inductive Ty : Type
| base : Ty
| arrow : (tIn : Ty) → (tOut : Ty) → Ty
deriving DecidableEq, Repr

scoped infixr:60 " :=> " => Ty.arrow

inductive Tm : Type
| var : TermVar -> Tm
| literal : Instructions -> Tm
| function : (TermVar -> Tm) -> Tm
| apply : (function : Tm) -> (argument : Tm) -> Tm

end

def Env (TermVar : Type) := List (TermVar × Ty)

namespace Env

section

variable {TermVar : Type}

@[simp] def empty : Env TermVar := []

@[simp] def extend (env : Env TermVar) (name : TermVar) (type : Ty) : Env TermVar :=
  (name, type) :: env

variable [DecidableEq TermVar]

@[simp] def get (name : TermVar) : Env TermVar → Option Ty
| [] => none
| (bound_name, type) :: env =>
    if name = bound_name then
      some type
    else
      get name env

@[simp] lemma get_extend_self (env : Env TermVar) (name : TermVar) (type : Ty) :
    (env.extend name type).get name = some type := by
  simp [get, extend]

@[simp] lemma get_extend_of_ne (env : Env TermVar) {tested_name name : TermVar} (type : Ty)
    (different : tested_name ≠ name) :
    (env.extend name type).get tested_name = env.get tested_name := by
  simp [get, extend, different]

inductive Checked : Env TermVar -> Tm -> Ty -> Type where
| var {env : Env TermVar} {name : TermVar} {type : Ty} :
    env.get name = some type ->
    Checked env (.var name) type
| literal {env : Env TermVar} (code : Instructions) :
    Checked env (.literal code) Ty.base
| function {env : Env TermVar} {body : TermVar -> Tm} {tyIn tyOut : Ty} :
    (∀ name : TermVar, Checked (env.extend name tyIn) (body name) tyOut) ->
    Checked env (.function body) (tyIn :=> tyOut)
| apply {env : Env TermVar} {function argument : Tm} {tyIn tyOut : Ty} :
    Checked env function (tyIn :=> tyOut) ->
    Checked env argument tyIn ->
    Checked env (.apply function argument) tyOut

abbrev Typing (env : Env TermVar) (term : Tm (TermVar := TermVar)) (type : Ty) : Prop :=
  Nonempty (Checked env term type)

@[simp] def IsScoped (env : Env TermVar) (term : Tm (TermVar := TermVar)) : Prop := ∃ type, env.Typing term type

/--
AKA well-typed term, every variable in the term is in the environment
-/
structure TermWithType (env : Env TermVar) (type : Ty) where
  term : Tm (TermVar := TermVar)
  checked : Checked env term type

end

end Env

def Ty.Denotation : (type : Ty) → Type
| .base => Instructions
| (tyIn :=> tyOut) => tyIn.Denotation → tyOut.Denotation

structure REPL (TermVar : Type) [DecidableEq TermVar] where
  env : Env TermVar
  varLookup : ∀ (name : TermVar) (type : Ty), (env.get name = some type) → Ty.Denotation type

namespace REPL

section

variable {TermVar : Type} [DecidableEq TermVar]

@[simp] def empty : REPL TermVar where
  env := []
  varLookup := fun _ _ binding => by
    cases binding

@[simp] def extend (repl : REPL TermVar) (name : TermVar)
    (value : Ty.Denotation input) : REPL TermVar where
  env := repl.env.extend name input
  varLookup := fun tested_name type binding =>
    if same_name : tested_name = name then
      by
        subst same_name
        simp at binding
        cases binding
        exact value
    else
      repl.varLookup tested_name type (by simpa [Env.extend, Env.get, same_name] using binding)

end

section

variable {TermVar : Type} [DecidableEq TermVar] [Inhabited TermVar]

/--
immediate evaluation of a new term

just a thin wrapper of the internal `impl`
-/
def eval (repl : REPL TermVar) (newTerm : repl.env.TermWithType type) : type.Denotation :=

  /-
  with heavy recursion, why is fuel not required?
  -/
  let rec impl {type : Ty} {term : Tm} (repl : REPL TermVar)
      (checked : repl.env.Checked term type) :
      type.Denotation :=
    match checked with
    | .literal normalForm => normalForm
    | .var binding => repl.varLookup _ _ binding
    | @Env.Checked.function _ _ _ body input output body_checked =>
        fun value =>
          impl (repl.extend (input := input) default value) (body_checked default)
    | @Env.Checked.apply _ _ _ function argument _ output function_checked argument_checked =>
        (impl repl function_checked) (impl repl argument_checked)

  impl repl newTerm.checked

@[simp] def canEvalTo (repl : REPL TermVar)
    (newTerm : repl.env.TermWithType type) (value : type.Denotation) : Prop :=
  repl.eval newTerm = value


end

end REPL

end STLC
